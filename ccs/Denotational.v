(* begin hide *)
From ITree Require Import
     ITree
     Eq.Eq
     Events.Exception
     ITreeFacts.

From CCS Require Import
     PropT
     Syntax
     Utils
.
Import ITreeNotations.
Open Scope itree.
Import CCSNotations.
Open Scope ccs_scope.

From Paco Require Import paco.

Section Semantics.

  Variant ActionE : Type -> Type :=
  | Act (a : action) : ActionE unit.

  Variant SynchE : Type -> Type := | Synch : SynchE unit.

  Variant choice := | Left | Right | Synchronize.

  Variant NonDetE : Type -> Type :=
  | Plus : NonDetE bool
  | Sched2 : NonDetE bool
  | Sched3 : NonDetE choice.

  Definition DeadE := exceptE unit.
  Definition dead {A : Type} {E} `{DeadE -< E} : itree E A :=
    x <- trigger (Throw tt);; match x: void with end.

  Notation ccsE   := (NonDetE +' ActionE +' SynchE +' DeadE).
  Notation ccsT T := (itree ccsE T).
  Notation ccs    := (ccsT unit).

  Definition done : ccs := Ret tt.

  Definition act (a : action) : ccs := trigger (Act a).

  Definition plus (P Q : ccs) : ccs :=
    b <- trigger Plus;;
    match b with
    | true => P
    | false => Q
    end.

  Definition branch2 (P Q : ccs) : ccs :=
    b <- trigger Sched2;;
    match b with
    | true => P
    | false => Q
    end.

  Definition branch3 (P Q R : ccs) : ccs :=
    b <- trigger Sched3;;
    match b with
    | Left => P
    | Right => Q
    | Synchronize => R
    end.

  Variant head :=
  | HDone
  | HSynch (P : ccs)
  | HAct (a : action) (P : ccs).

  (* Notations for patterns *)
  Notation "'schedP' e" := (inl1 e) (at level 10).
  Notation "'actP' e" := (inr1 (inl1 e)) (at level 10).
  Notation "'synchP' e" := (inr1 (inr1 (inl1 e))) (at level 10).
  Notation "'deadP' e" := (inr1 (inr1 (inr1 e))) (at level 10).

  Definition get_hd : ccs -> ccsT head :=
    cofix get_hd (P : ccs) :=
      match observe P with
      | RetF x => Ret HDone
      | TauF P => Tau (get_hd P)
      | @VisF _ _ _ T e k =>
        match e with
        | schedP e => vis e (fun x => get_hd (k x))
        | actP e =>
          match e in ActionE X return (T = X -> ccsT head) with
          | Act a => fun (Pf : T = unit) =>
                      Ret (HAct a (@eq_rect_r _ T (fun T => T -> itree ccsE unit) k unit (eq_sym Pf) tt))
          end eq_refl
        | synchP e =>
          match e in SynchE X return (T = X -> ccsT head) with
          | Synch => fun (Pf : T = unit) =>
                      Ret (HSynch (@eq_rect_r _ T (fun T => T -> itree ccsE unit) k unit (eq_sym Pf) tt))
          end eq_refl
        | deadP e => Ret HDone
        end
      end
  .

  Definition para_old : ccs -> ccs -> ccs :=
    cofix F (P : ccs) (Q : ccs) :=
      branch3
        (x <- get_hd P;;
         match x with
         | HDone => Q
         | HSynch P => vis Synch (fun _ => F P Q)
         | HAct a P => vis (Act a) (fun _ => F P Q)
         end
        )
        (x <- get_hd Q ;;
         match x with
         | HDone => P
         | HSynch Q => vis Synch (fun _ => F P Q)
         | HAct a Q => vis (Act a) (fun _ => F P Q)
         end
        )
        (rP <- get_hd P;;
         rQ <- get_hd Q;;
         match rP,rQ with
         | HAct a P, HAct b Q =>
           if are_opposite a b
           then vis Synch (fun _ => F P Q)
           else dead
         | _, _ => dead
         end
        )
  .

  Definition para : ccs -> ccs -> ccs :=
    cofix F (P : ccs) (Q : ccs) :=
      rP <- get_hd P;;
      rQ <- get_hd Q;;
      match rP, rQ with
      | HDone, HDone => done
      | HDone, _ => Q
      | _, HDone => P
      | HAct a P', HAct b Q' =>
        if are_opposite a b
        then
          branch3 (vis (Act a) (fun _ => F P' (vis (Act b) (fun _ => Q'))))
                  (vis (Act b) (fun _ => F (vis (Act a) (fun _ => P')) Q'))
                  (vis Synch   (fun _ => F P' Q'))
        else
          branch2 (vis (Act a) (fun _ => F P' (vis (Act b) (fun _ => Q'))))
                  (vis (Act b) (fun _ => F (vis (Act a) (fun _ => P')) Q'))
      | HAct a P', HSynch Q' =>
        branch2 (vis (Act a) (fun _ => F P' (vis Synch (fun _ => Q'))))
                (vis Synch   (fun _ => F (vis (Act a) (fun _ => P')) Q'))
      | HSynch P', HAct a Q' =>
        branch2 (vis Synch   (fun _ => F P' (vis (Act a) (fun _ => Q'))))
                (vis (Act a) (fun _ => F (vis Synch (fun _ => P')) Q'))
      | HSynch P', HSynch Q' =>
        branch2 (vis Synch   (fun _ => F P' (vis Synch (fun _ => Q'))))
                (vis Synch   (fun _ => F (vis Synch (fun _ => P')) Q'))
      end.

  Definition h_trigger {E F} `{E -< F} : E ~> itree F :=
    fun _ e => trigger e.

  Definition h_restrict (c : chan) : Handler ActionE ccsE :=
    fun _ e => let '(Act a) := e in
            match a with
            | Send c'
            | Rcv c' =>
              if c =? c' then dead else trigger e
            end.

  Definition restrict : chan -> ccs -> ccs :=
    fun c P =>
      interp (case_ h_trigger (case_ (h_restrict c) h_trigger)) P.

  Fixpoint model (t : term) : ccs :=
    match t with
    | DoneT         => done
    | ActionT a t   => act a;; model t
    | ParaT t1 t2   => para (model t1) (model t2)
    | PlusT t1 t2   => plus (model t1) (model t2)
    | RestrictT c t => restrict c (model t)
    end.

  Fixpoint model_old (t : term) : ccs :=
    match t with
    | DoneT         => done
    | ActionT a t   => act a;; model_old t
    | ParaT t1 t2   => para_old (model_old t1) (model_old t2)
    | PlusT t1 t2   => plus (model_old t1) (model_old t2)
    | RestrictT c t => restrict c (model_old t)
    end.

  (** A term can advance in a single step producing either an action or a synchronisation,
   *  encoded here as None *)
  Inductive step : ccs -> option action -> ccs -> Prop :=
  (* Tau *)
  | S_Tau : forall a P P' Q,
       step P a Q ->
       P' ≅ Tau P ->
       step P' a Q
  (* Simple action *)
  | S_Act : forall a P P',
       P' ≅ act a ;; P ->
       step P' (Some a) P
  (* Synchronisation *)
  | S_Synch : forall P P',
       P' ≅ trigger Synch ;; P ->
       step P' None P
  (* Choice *)
  | S_Plus_L : forall a P L L' R,
      step L a L' ->
      P ≅ plus L R ->
      step P a L'
  | S_Plus_R : forall a P L R R',
      step R a R' ->
      P ≅ plus L R ->
      step P a R'
  (* Two-way parallelism *)
  | S_Sched2_L : forall a P P' L L' R,
      step L a L' ->
      P ≅ branch2 L R ->
      P' ≅ branch2 L' R ->
      step P a P'
  | S_Sched2_R : forall a P P' L R R',
      step R a R' ->
      P ≅ branch2 L R ->
      P' ≅ branch2 L R' ->
      step P a P'
  (* Three-way parallelism *)
  | S_Sched3_L : forall a P P' L L' R S,
      step L a L' ->
      P ≅ branch3 L R S ->
      P' ≅ branch3 L' R S ->
      step P a P'
  | S_Sched3_R : forall a P P' L R R' S,
      step R a R' ->
      P ≅ branch3 L R S ->
      P' ≅ branch3 L R' S ->
      step P a P'
  | S_Sched3_S : forall a P P' L R S S',
      step S a S' ->
      P ≅ branch3 L R S ->
      P' ≅ branch3 L R S' ->
      step P a P'.

  CoInductive bisim_old : ccs -> ccs -> Prop :=
    BiSim : forall P Q,
      ((forall a P' (PStep : step P a P'), exists Q', step Q a Q' /\ bisim_old P' Q')
       /\ (forall a Q' (QStep : step Q a Q'), exists P', step P a P' /\ bisim_old P' Q'))
      -> bisim_old P Q.

  (* Paco stuff *)
  Variant bisim_gen bisim : ccs -> ccs -> Prop :=
    _bisim_gen : forall P Q,
      ((forall a P' (PStep : step P a P'), exists Q', step Q a Q' /\ bisim P' Q')
       /\ (forall a Q' (QStep : step Q a Q'), exists P', step P a P' /\ bisim P' Q'))
      -> bisim_gen bisim P Q.
  Hint Constructors bisim_gen : core.

  Definition bisim' P Q : Prop := paco2 bisim_gen bot2 P Q.
  Hint Unfold bisim' : core.

  Lemma bisim_gen_mon : monotone2 bisim_gen.
  Proof.
    unfold monotone2.
    intros.
    inversion IN; subst.
    destruct H as [Hx0 Hx1].
    econstructor.
    split;
      intros;
      (apply Hx0 in PStep as [x' [xStep RPQ]] ||
       apply Hx1 in QStep as [x' [xStep RPQ]]);
      exists x';
      eauto.
  Qed.
  Hint Resolve bisim_gen_mon : paco.

  Theorem bisim_refl: forall P, bisim_old P P.
  Proof.
    cofix H.
    constructor.
    split; eauto.
  Qed.

  Theorem bisim_refl': forall P, bisim' P P.
  Proof.
    pcofix H.
    intros.
    pfold.
    econstructor.
    split; eauto.
  Qed.

  Theorem bisim_commu: forall P Q, bisim_old P Q -> bisim_old Q P.
  Proof.
    cofix CIH.
    intros P Q HPQ.
    inversion HPQ; subst.
    destruct H as [QSimP PSimQ].
    constructor.
    split.
    - intros a Q' QStep.
      apply PSimQ in QStep as [P' [PStep H'PQ]].
      eauto.
    - intros a P' PStep.
      apply QSimP in PStep as [Q' [QStep H'PQ]].
      eauto.
  Qed.

  Theorem bisim_commu': forall P Q, bisim' P Q -> bisim' Q P.
  Proof.
    pcofix CIH.
    intros P Q HPQ.
    pinversion HPQ; subst.
    destruct H as [QSimP PSimQ].
    pfold.
    econstructor.
    split.
    - intros a Q' QStep.
      apply PSimQ in QStep as [P' [PStep H'PQ]].
      pclearbot. (* in H'PQ *)
      exists P'.
      eauto.
    - intros a P' PStep.
      apply QSimP in PStep as [Q' [QStep H'PQ]].
      pclearbot. (* in H'PQ *)
      exists Q'.
      eauto.
  Qed.

  Theorem bisim_trans: forall P Q R, bisim_old P Q -> bisim_old Q R -> bisim_old P R.
  Proof.
    cofix CIH.
    intros P Q R HPQ HQR.
    constructor.
    split.
    - intros.
      inversion HPQ; subst.
      destruct H as [QSimP _].
      apply QSimP in PStep as [Q' [QStep H'PQ]].
      inversion HQR; subst.
      destruct H as [RSimQ _].
      apply RSimQ in QStep as [R' [RStep H'QR]].
      eauto.
    - intros a R' RStep.
      inversion HQR; subst.
      destruct H as [_ QSimR].
      apply QSimR in RStep as [Q' [QStep H'QR]].
      inversion HPQ; subst.
      destruct H as [_ PSimQ].
      apply PSimQ in QStep as [P' [PStep H'PQ]].
      eauto.
  Qed.

  Theorem bisim_trans': forall P Q R, bisim' P Q -> bisim' Q R -> bisim' P R.
  Proof.
    pcofix CIH.
    intros P Q R HPQ HQR.
    apply CIH with (P := P) in HQR as HPR; [| apply HPQ].
    pfold.
    econstructor.
    split.
    (* the reasoning behind both branches is roughly the same,
       but the order changes so I can't merge them neatly *)
    - intros a P' PStep.
      pinversion HPQ; subst.
      destruct H as [QSimP _].
      apply QSimP in PStep as [Q' [QStep H'PQ]].
      pinversion HQR; subst.
      destruct H as [RSimQ _].
      apply RSimQ in QStep as [R' [RStep H'QR]].
      pclearbot. (* in H'QR *)
      exists R'.
      eauto.
    - intros a R' RStep.
      pinversion HQR; subst.
      destruct H as [_ QSimR].
      apply QSimR in RStep as [Q' [QStep H'PR]].
      pinversion HPQ; subst.
      destruct H as [_ PSimQ].
      apply PSimQ in QStep as [P' [PStep H'PQ]].
      pclearbot. (* in H'PQ *)
      exists P'.
      eauto.
  Qed.

  Lemma step_tau_inv :
    forall P a Q, step (Tau P) a Q -> step P a Q.
  Proof.
    intros.
    inversion H; subst; auto.
    (* apply eqit_inv in H1. *)
    all: admit.
  Admitted.

  Lemma example1: bisim_old (act (↓ "a") ;; done)
                            (Tau (act (↓ "a");; done)).
  Proof.
    constructor.
    split; intros.
    - exists P'.
      split.
      + now apply S_Tau with (P := (act (↓ "a");; done)).
      + apply bisim_refl.
    - exists Q'.
      split.
      + now apply step_tau_inv.
      + apply bisim_refl.
  Qed.

  Lemma example1': bisim' (act (↓ "a") ;; done)
                          (Tau (act (↓ "a");; done)).
  Proof.
    pfold.
    constructor.
    split.
    - intros.
      exists P'.
      split; [| left; apply bisim_refl'].
      now apply S_Tau with (P := (act (↓ "a");; done)).
    - intros.
      exists Q'.
      split; [| left; apply bisim_refl'].
      apply step_tau_inv; auto.
  Qed.

End Semantics.

(* Notations for patterns *)
Notation "'schedP' e" := (inl1 e) (at level 10).
Notation "'actP' e" := (inr1 (inl1 e)) (at level 10).
Notation "'synchP' e" := (inr1 (inr1 (inl1 e))) (at level 10).
Notation "'deadP' e" := (inr1 (inr1 (inr1 e))) (at level 10).

From CCS Require Import
  Operational.

Section EquivSem.

  Notation step_ccs := Denotational.step.
  Notation step_op  := Operational.step.

  Notation ccsE   := (NonDetE +' ActionE +' SynchE +' DeadE).
  Notation ccsT T := (itree ccsE T).
  Notation ccs    := (ccsT unit).

  (* Lifting the operational stepping over itrees to the syntax
  via representation *)
  Definition step_sem : term -> option action -> term -> Prop :=
    fun t1 ma t2 => step_ccs (model t1) ma (model t2).

  (* Lock-step bisimulation between terms and [ccs] *)
  Variant bisimF bisim : term -> term -> Prop :=
    _bisimF : forall P Q,
      ((forall a P' (PStep : step_op P a P'),
           exists Q', step_sem Q a Q' /\ bisim P' Q')
       /\ (forall a Q' (QStep : step_sem Q a Q'),
             exists P', step_op P a P' /\ bisim P' Q'))
      -> bisimF bisim P Q.
  Hint Constructors bisimF : core.

  Definition bisim := paco2 bisimF bot2.
  Hint Unfold bisim : core.

  Lemma bisimF_mon : monotone2 bisimF.
  Proof.
    unfold monotone2.
    intros.
    inversion IN; subst.
    destruct H as [StepOp StepSem].
    econstructor.
    split; intros.
    - apply StepOp in PStep as [Q' [Sem2 RPQ]].
      eauto.
    - apply StepSem in QStep as [P' [Op2 RPQ]].
      eauto.
  Qed.
  Hint Resolve bisimF_mon : paco.


  Definition headify a :=
    match a with
    | Some a => HAct a
    | None => HSynch
    end.

  Inductive Returns_legacy {E} {A: Type} (a: A) : itree E A -> Prop :=
  | Returns_legacyRet: forall t, t ≅ Ret a -> Returns_legacy a t
  | Returns_legacyTau: forall t u, t ≅ Tau u -> Returns_legacy a u -> Returns_legacy a t
  | Returns_legacyVis: forall {X} (e: E X) (x: X) t k, t ≅ Vis e k -> Returns_legacy a (k x) -> Returns_legacy a t.

  Inductive Returns {A: Type} (a: A) : ccsT A -> Prop :=
  | ReturnsRet: forall t, t ≅ Ret a -> Returns a t
  | ReturnsTau: forall t u, t ≅ Tau u -> Returns a u -> Returns a t
  | ReturnsChoiceL: forall (t P Q: ccsT A),
      t ≅ Vis (inl1 Plus) (fun b: bool => if b then P else Q) ->
      Returns a P -> Returns a t
  | ReturnsChoiceR: forall t P Q,
      t ≅ Vis (inl1 Plus) (fun b: bool => if b then P else Q) ->
      Returns a Q -> Returns a t
  | ReturnsPara2L: forall t P Q,
      t ≅ Vis (inl1 Sched2) (fun b: bool => if b then P else Q) ->
      Returns a P -> Returns a t
  | ReturnsPara2R: forall t P Q,
      t ≅ Vis (inl1 Sched2) (fun b: bool => if b then P else Q) ->
      Returns a Q -> Returns a t
  | ReturnsPara3L: forall t P Q R,
      t ≅ Vis (inl1 Sched3) (fun c => match c with
                                   | Left => P
                                   | Right => Q
                                   | Synchronize => R
                                   end) ->
      Returns a P -> Returns a t
  | ReturnsPara3R: forall t P Q R,
      t ≅ Vis (inl1 Sched3) (fun c => match c with
                                   | Left => P
                                   | Right => Q
                                   | Synchronize => R
                                   end) ->
      Returns a Q -> Returns a t
  | ReturnsPara3S: forall t P Q R,
      t ≅ Vis (inl1 Sched3) (fun c => match c with
                                   | Left => P
                                   | Right => Q
                                   | Synchronize => R
                                   end) ->
      Returns a R -> Returns a t.

  Section Inversion_Lemma.

    (* TODO: Push some stuff in the itree library *)

    Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

    Lemma eqitree_inv_Tau_r (t : itree E R1) t' :
      eq_itree RR t (Tau t') -> exists t0, observe t = TauF t0 /\ eq_itree RR t0 t'.
    Proof.
      intros.
      punfold H.
      inv H;
        try inv CHECK;
        pclearbot;
        eauto.
    Qed.

    Lemma eqitree_inv_Tau_l (t : itree E R1) t' :
      eq_itree RR (Tau t) t' -> exists t0, observe t' = TauF t0 /\ eq_itree RR t t0.
    Proof.
      intros; punfold H; inv H; try inv CHECK; pclearbot; eauto.
    Qed.

    Lemma eqitree_inv_Ret_r (t : itree E R1) r :
      eq_itree RR t (Ret r) -> exists r', RR r' r /\ observe t = RetF r'.
    Proof.
      intros; punfold H; inv H; try inv CHECK; eauto.
    Qed.

    Lemma eqitree_inv_Ret_l (t : itree E R2) r :
      eq_itree RR (Ret r) t -> exists r', RR r r' /\ observe t = RetF r'.
    Proof.
      intros; punfold H; inv H; try inv CHECK; eauto.
    Qed.

    Lemma eqitF_inv_VisF_l {b1 b2 vclo sim}
      X1 (e1 : E X1) (k1 : X1 -> _) t2 :
       eqitF RR b1 b2 vclo sim (VisF e1 k1) t2 ->
       (exists k2, t2 = VisF e1 k2 /\ forall v, vclo sim (k1 v) (k2 v)) \/
       (b2 = true /\ exists t2', t2 = TauF t2' /\ eqitF RR b1 b2 vclo sim  (VisF e1 k1) (observe t2')).
    Proof.
      refine (fun H =>
        match H in eqitF _ _ _ _ _ t1 _ return
        match t1 return Prop with
        | VisF e1 k1 => _
        | _ => True
        end
      with
      | EqVis _ _ _ _ _ _ _ _ _ => _
      | _ => _
      end); try exact I.
      - left; eauto.
      - destruct i; eauto.
    Qed.

    Lemma eqitree_inv_Vis_r {U} (t : itree E R1) (e : E U) (k : U -> itree E R2) :
      eq_itree RR t (Vis e k) -> exists k', observe t = VisF e k' /\ forall u, eq_itree RR (k' u) (k u).
    Proof.
      intros.
      punfold H.
      apply eqitF_inv_VisF_r in H.
      destruct H as [ [? [-> ?]] | [] ]; [ | discriminate ].
      pclearbot.
      eexists; split; eauto.
    Qed.

    Lemma eqitree_inv_Vis_l {U} (t : itree E R2) (e : E U) (k : U -> _) :
      eq_itree RR (Vis e k) t -> exists k', observe t = VisF e k' /\ forall u, eq_itree RR (k u) (k' u).
    Proof.
      intros; punfold H; apply eqitF_inv_VisF_l in H.
      destruct H as [ [? [-> ?]] | [] ]; [ | discriminate ].
      pclearbot. eexists; split; eauto.
    Qed.

    Lemma eqitree_tau_ret_abs : forall (t : itree E R1) x,
      eq_itree RR (Tau t) (Ret x) -> False.
    Proof.
      intros; edestruct @eqitree_inv_Tau_l as (? & abs &?); eauto; inv abs.
    Qed.

    Lemma eqitree_ret_tau_abs : forall (t : itree E R2) x,
      eq_itree RR (Ret x) (Tau t) -> False.
    Proof.
     intros; edestruct @eqitree_inv_Tau_r as (? & abs &?); eauto; inv abs.
    Qed.

    Lemma eqitree_ret_vis_abs : forall {U} e (k : U -> itree E R2) x,
      eq_itree RR (Ret x) (Vis e k) -> False.
    Proof.
     intros; edestruct @eqitree_inv_Vis_r as (? & abs &?); eauto; inv abs.
    Qed.

    Lemma eqitree_vis_ret_abs : forall {U} e (k : U -> itree E R1) x,
      eq_itree RR (Vis e k) (Ret x) -> False.
    Proof.
      intros; edestruct @eqitree_inv_Vis_l as (? & abs &?); eauto; inv abs.
    Qed.

    Lemma eqitree_vis_tau_abs : forall {U} e (k : U -> itree E R1) t,
      eq_itree RR (Vis e k) (Tau t) -> False.
    Proof.
      intros; edestruct @eqitree_inv_Vis_l as (? & abs &?); eauto; inv abs.
    Qed.

    Lemma eqitree_tau_vis_abs : forall {U} e (k : U -> itree E R2) t,
      eq_itree RR (Tau t) (Vis e k) -> False.
    Proof.
      intros; edestruct @eqitree_inv_Vis_r as (? & abs &?); eauto; inv abs.
    Qed.

  End Inversion_Lemma.

  Ltac inv_eqitree H :=
    match type of H with
    | eq_itree _ (Tau _) (Ret _)   => apply eqitree_tau_ret_abs in H; contradiction
    | eq_itree _ (Ret _) (Tau _)   => apply eqitree_ret_tau_abs in H; contradiction
    | eq_itree _ (Vis _ _) (Ret _) => apply eqitree_vis_ret_abs in H; contradiction
    | eq_itree _ (Ret _) (Vis _ _) => apply eqitree_ret_vis_abs in H; contradiction
    | eq_itree _ (Vis _ _) (Tau _) => apply eqitree_vis_tau_abs in H; contradiction
    | eq_itree _ (Tau _) (Vis _ _) => apply eqitree_tau_vis_abs in H; contradiction
    | eq_itree _ (Ret _) (Ret _)   => apply eqit_inv_Ret in H
    | _ => idtac
    end.

  From Coq Require Import Morphisms.

  Notation get_hd_ P :=
    match observe P with
    | RetF x => Ret HDone
    | TauF P => Tau (get_hd P)
    | @VisF _ _ _ T e k =>
      match e with
      | schedP e => vis e (fun x => get_hd (k x))
      | actP e =>
        match e in ActionE X return (T = X -> ccsT head) with
        | Act a => fun (Pf : T = unit) =>
                    Ret (HAct a (@eq_rect_r _ T (fun T => T -> itree ccsE unit) k unit (eq_sym Pf) tt))
        end eq_refl
      | synchP e =>
        match e in SynchE X return (T = X -> ccsT head) with
        | Synch => fun (Pf : T = unit) =>
                    Ret (HSynch (@eq_rect_r _ T (fun T => T -> itree ccsE unit) k unit (eq_sym Pf) tt))
        end eq_refl
      | deadP e => Ret HDone
      end
    end
  .

  Lemma get_hd_unfold : forall P,
    get_hd P ≅ get_hd_ P.
  Proof.
    intros.
    apply observing_sub_eqit.
    constructor.
    reflexivity.
  Qed.

  Definition eq_head : head -> head -> Prop :=
  fun h1 h2 =>
  match h1,h2 with
   | HDone, HDone => True
   | HSynch t1, HSynch t2 => t1 ≅ t2
   | HAct a1 t1, HAct a2 t2 => a1 = a2 /\ t1 ≅ t2
   | _, _ => False
  end.
  Hint Unfold eq_head : core.

  Global Instance get_hd_eq_itree :
    Proper (eq_itree eq ==> eq_itree eq_head) get_hd.
  Proof.
    do 2 red.
    ginit.
    gcofix CIH.
    intros * EQ.
    punfold EQ.
    setoid_rewrite get_hd_unfold.
    induction EQ; try inv CHECK.
    - gstep; constructor; reflexivity.
    - gstep; pclearbot. constructor; auto with paco.
    - gstep; pclearbot.
      destruct e as [? | [? | [? | ?]]].
      + constructor; red; auto with paco.
      + destruct a; constructor; auto.
      + destruct s; constructor; auto.
      + constructor; auto.
  Qed.

  Global Instance eq_itree_step_ccs :
    Proper (eq_itree eq ==> eq ==> eq_itree eq ==> flip impl) step_ccs.
  Proof.
    do 6 red; intros * EQ1 * -> * EQ2 STEP.
    revert x EQ1 x0 EQ2.
    induction STEP; intros.
    - apply S_Tau with P.
      + now apply IHSTEP.
      + etransitivity; eauto.
    - apply S_Act; rewrite EQ1,H; apply eqit_bind; [reflexivity | intros ?; symmetry; auto].
    - apply S_Synch; rewrite EQ1,H; apply eqit_bind; [reflexivity | intros ?; symmetry; auto].
    - eapply S_Plus_L; [| rewrite EQ1; eauto].
      apply IHSTEP; [reflexivity | auto].
    - eapply S_Plus_R; [| rewrite EQ1; eauto].
      apply IHSTEP; [reflexivity | auto].
    - eapply S_Sched2_L; [| rewrite EQ1; eauto | rewrite EQ2; eauto].
      apply IHSTEP; [reflexivity | reflexivity].
    - eapply S_Sched2_R; [| rewrite EQ1; eauto | rewrite EQ2; eauto].
      apply IHSTEP; [reflexivity | reflexivity].
    - eapply S_Sched3_L ; [| rewrite EQ1; eauto | rewrite EQ2; eauto].
      apply IHSTEP; [reflexivity | reflexivity].
    - eapply S_Sched3_R ; [| rewrite EQ1; eauto | rewrite EQ2; eauto].
      apply IHSTEP; [reflexivity | reflexivity].
    - eapply S_Sched3_S ; [| rewrite EQ1; eauto | rewrite EQ2; eauto].
      apply IHSTEP; [reflexivity | reflexivity].
  Qed.

  Inductive Finite {E X} : itree E X -> Prop :=
  | FRet : forall x t, t ≅ Ret x -> Finite t
  | FTau : forall P t, t ≅ Tau P -> Finite P -> Finite t
  | FVis : forall {A} (e: E A) k t,
      t ≅ Vis e k -> (forall x, Finite (k x)) -> Finite t.

  Inductive FiniteSchedTree {X} : itree ccsE X -> Prop :=
  | FSTRet : forall {A} R t (x: A), eq_itree R t (Ret x) -> FiniteSchedTree t
  | FSTTau : forall R t P, eq_itree R t (Tau P) -> FiniteSchedTree P -> FiniteSchedTree t
  | FSTPlus : forall R t k,
      eq_itree R t (b <- trigger Plus;; k b) ->
      (forall b, FiniteSchedTree (k b)) ->
      FiniteSchedTree t
  | FSTSched2 : forall R t k,
      eq_itree R t (b <- trigger Sched2;; k b) ->
      (forall b, FiniteSchedTree (k b)) ->
      FiniteSchedTree t
  | FSTSched3 : forall R t k,
      eq_itree R t (c <- trigger Sched3;; k c) ->
      (forall c, FiniteSchedTree (k c)) ->
      FiniteSchedTree t.

  Global Instance Finite_eq_itree {E X} :
    Proper (eq_itree eq ==> flip impl) (@Finite E X).
  Proof.
    do 4 red.
    intros x y Cong Fin.
    revert x Cong.
    induction Fin;
      intros.
    - apply FRet with x.
      now rewrite Cong.
    - apply eqitree_inv_Tau_r in H.
      destruct H as [t' [Obs Cong']].
      apply FTau with t'.
      + rewrite Cong.
        now rewrite itree_eta, Obs.
      + now apply IHFin.
    - apply eqitree_inv_Vis_r in H.
      destruct H as [t' [Obs Cong']].
      eapply FVis.
      + rewrite Cong.
        now rewrite itree_eta, Obs.
      + intro.
        apply H1 with x0.
        apply Cong'.
  Qed.

  Global Instance FST_eq_itree {X} :
    forall R, Proper (eq_itree R ==> flip impl) (@FiniteSchedTree X).
  Proof.
    do 4 red.
    intros R x y Cong Fin.
    revert R x Cong.
    induction Fin;
      intros.
    - apply FSTRet with R x.
      (* now rewrite Cong. *)
      admit.
    - apply eqitree_inv_Tau_r in H.
      destruct H as [t' [Obs Cong']].
      apply FSTTau with R P.
      + (* rewrite Cong.
           rewrite itree_eta, Obs.
           now rewrite Cong'. *)
        admit.
      + apply IHFin with R0.
        admit.
    - apply FSTPlus with R k.
      (* rewrite Cong.
         all: assumption. *)
      all: admit.
    - apply FSTSched2 with R k.
      (* rewrite Cong.
         all: assumption. *)
      all: admit.
    - apply FSTSched3 with R k.
      (* rewrite Cong.
         all: assumption. *)
      all: admit.
  Admitted.

  (* This feels like it could be simpler *)
  Theorem finite_head : forall P, Finite P -> FiniteSchedTree (get_hd P).
  Proof.
    intros.
    induction H.
    - (* Ret *)
      pose proof (get_hd_unfold (Ret x)) as Eq;
        cbn in Eq.
      apply FSTRet with eq_head HDone.
      apply get_hd_eq_itree in H.
      now rewrite Eq in H.
    - (* Tau *)
      pose proof (get_hd_unfold (Tau P)) as Eq;
        cbn in Eq.
      rewrite H, Eq.
      now apply FSTTau with eq (get_hd P).
    - (* Vis *)
      rewrite H.
      induction e.
      + (* Vis NonDetE *)
        pose proof (get_hd_unfold (Vis (schedP n) k)) as Eq;
          cbn in Eq.
        rewrite Eq.
        induction n;
          [ apply FSTPlus with eq (fun x => get_hd (k x))
          | apply FSTSched2 with eq (fun x => get_hd (k x))
          | apply FSTSched3 with eq (fun x => get_hd (k x))];
          (now rewrite bind_trigger || assumption).
      + induction s.
        * (* Vis Act *)
          induction a.
          pose proof (get_hd_unfold (Vis (actP (Act a)) k)) as Eq;
            cbn in Eq.
          rewrite Eq.
          now apply FSTRet with eq (HAct a (k tt)).
        * induction s.
          -- (* Vis Synch *)
            induction s.
            pose proof (get_hd_unfold (Vis (synchP Synch) k)) as Eq;
              cbn in Eq.
            rewrite Eq.
            now apply FSTRet with eq (HSynch (k tt)).
          -- (* Vis Dead *)
            induction d.
            pose proof (get_hd_unfold (Vis (deadP (Throw u)) k)) as Eq;
              cbn in Eq.
            rewrite Eq.
            now apply FSTRet with eq HDone.
  Qed.

  Theorem finite_model : forall P, Finite (model P).
  Proof.
    induction P.
    - cbn.
      unfold done.
      apply FRet with tt.
      reflexivity.
    - cbn.
      Print FVis.
    all: admit.
  Admitted.

  Lemma get_hd_FST : forall P, FiniteSchedTree (get_hd (model P)).
  Proof.
    intros; eapply finite_head, finite_model.
  Qed.

(* para (model P) (model Q) ~~
   x <- get_hd P;
   y <- get_hd Q;
   Sched de la bonne action

*)

  Lemma FST_prefix_can_step : forall {X} (t : itree ccsE X) (k : X -> ccs) x a t',
    FiniteSchedTree t ->
    step_ccs (k x) a t' ->
    step_ccs (x <- t;; k x) a t'.
  Admitted.

  Theorem step_ccs_get_hd_returns : forall P a P',
      step_ccs P a P'
      ->
      Returns_legacy (headify a P') (get_hd P).
  Proof.
 Admitted.

  Theorem get_hd_means_step_deprecated : forall P a P',
      Returns_legacy (headify a P') (get_hd P)
      <->
      step_ccs P a P'.
  Proof.
    split; intros.
    - (* Returns -> step :
       * if a finite path exists in the [get_hd] tree, it
       * can be used as a proof tree to justify a [step_ccs] *)
      remember (headify a P') as aP'.
      remember (get_hd P) as head_P.
      revert P Heqhead_P.
      (* By induction on the path in the tree *)
      induction H.
      + (* [get_hd P] is a [Ret x], we derive information on the shape of P *)
        intros; subst.
        pose proof (itree_eta P) as EQ.
        rewrite EQ.
        apply get_hd_eq_itree in EQ.
        rewrite H in EQ; clear H.
        destruct (observe P).
        * (* Can't be a Ret *)
          rewrite get_hd_unfold in EQ; cbn in EQ.
          inv_eqitree EQ.
          destruct a; cbn in EQ; contradiction.
        * (* Can't be a Tau *)
          rewrite get_hd_unfold in EQ; cbn in EQ.
          inv_eqitree EQ.
        * rewrite get_hd_unfold in EQ; cbn in EQ.
          destruct e; cbn; inv_eqitree EQ.
          destruct s; cbn.
          destruct a0; cbn; inv_eqitree EQ.
          destruct a; cbn in EQ; try contradiction.
          destruct EQ as [<- EQ].
          constructor.
          unfold act; rewrite bind_trigger; apply eqit_Vis; intros [].
          symmetry; auto.
          destruct s; cbn; inv_eqitree EQ.
          destruct s; cbn; inv_eqitree EQ.
          destruct a; cbn in EQ; try contradiction.
          constructor.
          rewrite bind_trigger; apply eqit_Vis; intros [].
          symmetry; auto.
          destruct a; cbn in EQ; contradiction.
      + (* [get_hd] starts with a [Tau] *)
        intros; subst.
        pose proof (itree_eta P) as EQ.
        rewrite EQ.
        apply get_hd_eq_itree in EQ.
        rewrite H in EQ; clear H.
        destruct (observe P);
          rewrite get_hd_unfold in EQ;
          cbn in EQ;
          inv_eqitree EQ.
        * admit.
        * destruct e; cbn in *; inv_eqitree EQ.
          destruct s; cbn in *; inv_eqitree EQ.
          destruct a0; cbn in *; inv_eqitree EQ.
          destruct s; cbn in *; inv_eqitree EQ.
          destruct s; cbn in *; inv_eqitree EQ.
      (*
        eapply S_Tau; [apply IHReturns_legacy |].
        admit.
        admit. *)
      + intros; subst.
        pose proof (itree_eta P) as EQ; rewrite EQ; apply get_hd_eq_itree in EQ.
        rewrite H in EQ; clear H.
        destruct (observe P); rewrite get_hd_unfold in EQ; cbn in EQ; inv_eqitree EQ.
        destruct e0; cbn in *; inv_eqitree EQ.
        * admit.
        * destruct s; cbn in *; inv_eqitree EQ.
          destruct a0; cbn in *; inv_eqitree EQ.
          destruct s; cbn in *; inv_eqitree EQ.
          destruct s; cbn in *; inv_eqitree EQ.
   - (* Step -> Returns *)
      induction H.
      + admit.
      + admit.
  Admitted.

(* para P Q ~~ get_hd P;; get_hd Q;; fait la comm
  step_ccs t a t' -> step_ccs (get_hd P;;

*)


  Theorem get_hd_always_returns : forall P, exists a k, Returns (headify a k) (get_hd (model P)).
  Proof.
    induction P.
    - simpl.
      Print headify.
      Check Returns.
  Abort.

    (* écrire :
      prédicat finite
      pour tout P, finite model P
      finite P -> finite (get_hd P)

     écrire (et prouver)
      pour tout P, exists a k, Returns++ (a,k) (get_hd (model P))

     réfléchir à comment écrire
      ????
      Returns++ (a,k) P -> step (c a) b Q -> step (P ;; c) b q
      "si la deuxième moitié du para passe (wrt. step), la première devrait passer aussi parce que les get_hds sont finis"
      ????
     *)

  Theorem model_correct_complete :
    forall P, bisim P P.
  Proof.
    pcofix CIH.
    intros P.
    pfold.
    econstructor.
    split.
    - (* The denotational side can simulate the operational semantics *)
      intros a P' StepOp.
      exists P'.
      split; [| right; auto].
      clear CIH r.
      induction StepOp; try now constructor.
      + clear StepOp.
        red.
        cbn.
        red in IHStepOp.
        admit.
      + admit.
      + clear StepOp.
        red; red in IHStepOp.
        cbn.
        admit.
        (*

          (ax,kP) <- get_hd P;
          (ay,kQ) <- get_hd Q;
          b <- Sched2;
           true -> trigger ax;; para (kP tt) Q
           false -> trigger ay;; para P (kQ tt)

           step_ccs (model P) !b ∅

           get_hd (choice2 (true -> !a ; false -> !b))

           choice2 (true -> !a,∅; false -> !b,∅

           step_ccs (model P) a (model P') est un chemin
           dans get_hd (model P) qui mène à la feuille (a,model P')
           ~> "step_ccs like (get_hd (model P)) a (model P')"

           step_ccs (model P) explore un chemin prefix de choices de (model P)
           step_ccs (para (model P) (model Q))
              explore le même chemin prefix de choices,
              mais dans l'arbre prefix get_hd (model P)

            )

          para t u :
           a,k <- get_hd t; a',k' <- get_hd u ;
           choice3


        *)
      + admit.
      + admit.
      + admit.

(*
      rename P' into Po.
        destruct IHStepOp as [Ps [StepSem R]].
        exists (Ps ∥ Q).
        split.
        * Print S_Vis_Sched2_L.
          admit.
        * admit. *)

    - (* The operational side can simulate the denotational semantics *)
      intros a P' StepSem.
      exists P'; split; [| auto].
     admit.
  Admitted.

End EquivSem.
