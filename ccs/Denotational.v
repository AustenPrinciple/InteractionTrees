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
  | S_Tau : forall t a P Q,
      t ≅ Tau P -> step P a Q -> step t a Q
  (* Simple action *)
  | S_Vis_Act : forall t a P,
      t ≅ act a ;; P -> step t (Some a) P
  (* Synchronisation *)
  | S_Vis_Synch : forall t P,
      t ≅ trigger Synch ;; P -> step t None P
  (* Choice *)
  | S_Vis_Plus_L : forall t a L L' R,
      t ≅ plus L R -> step L a L' -> step t a L'
  | S_Vis_Plus_R : forall t a L R R',
      t ≅ plus L R -> step R a R' -> step t a R'
  (* Two-way parallelism *)
  | S_Vis_Sched2_L : forall t a L L' R,
      t ≅ branch2 L R -> step L a L' -> step t a (branch2 L' R)
  | S_Vis_Sched2_R : forall t a L R R',
      t ≅ branch2 L R -> step R a R' -> step t a (branch2 L R')
  (* Three-way parallelism *)
  | S_Vis_Sched3_L : forall t a L L' R S,
      t ≅ branch3 L R S -> step L a L' -> step t a (branch3 L' R S)
  | S_Vis_Sched3_R : forall t a L R R' S,
      t ≅ branch3 L R S -> step R a R' -> step t a (branch3 L R' S)
  | S_Vis_Sched3_S : forall t a L R S S',
      t ≅ branch3 L R S -> step S a S' -> step t a (branch3 L R S').

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
      admit.
  Abort.

  Lemma step_tau_inv :
    forall P a Q, step (Tau P) a Q -> step P a Q.
  Proof.
    intros.
    inversion H; subst; auto.
    (* apply eqit_inv in H1. *)
    all: admit.
  Admitted.

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

  Lemma no_step_done : forall a P, not (step_op 0 a P).
  Proof.
    unfold not.
    intros.
    inversion H.
  Qed.

  Definition headify a :=
    match a with
    | Some a => HAct a
    | None => HSynch
    end.

  (* replaced \approx with \cong *)
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

  Inductive Finite {E X} : itree E X -> Prop :=
  | FRet : forall x, Finite (Ret x)
  | FTau : forall P, Finite P -> Finite (Tau P)
  | FVis : forall {A} (e: E A) x k, Finite (k x) -> Finite (Vis e k).

  Theorem finite_head : forall P, Finite P -> Finite (get_hd P).
  Proof.
    intros.
    induction H.
    all: admit.
  Abort.

  Theorem finite_model : forall P, Finite (model P).
  Proof.
    induction P.
    - constructor.
    - admit.
    all: admit.
  Abort.

  Theorem machin : forall P, exists a k, Returns (headify a k) (get_hd (model P)).
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
  Theorem get_hd_means_step : forall P a P',
      Returns (headify a P') (get_hd P)
      <->
      step_ccs P a P'.
  Proof.
    split; intros.
    - (* Returns -> step *)
      remember (headify a P') as aP'.
      remember (get_hd P) as hd_P.
      revert P Heqhd_P.
      induction H; admit.
    - (* Step -> Returns *)
      induction H.
      + admit.
      + admit.
  Admitted.

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
        (*
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
