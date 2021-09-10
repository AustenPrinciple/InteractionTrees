(* begin hide *)
From Coq Require Import
     Morphisms
     Program.Equality.

From ITree Require Import
     ITree
     Eq.Eq
     Events.Exception
     ITreeFacts.

From CCS Require Import
     PropT
     Syntax
     Utils
     Operational
     Denotational
.
Import ITreeNotations.
Open Scope itree.
Import CCSNotations.
Import DenNotations.
Open Scope ccs_scope.

From Paco Require Import paco.
From Coq Require Import Morphisms.
(* end hide *)

  Ltac break_match_goal :=
    match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
      | sumbool _ _ => destruct X
      | _ => destruct X eqn:?
      end
    end.

  Ltac break_match_hyp h :=
    match type of h with
    | context [ match ?X with _ => _ end ] =>
      match type of X with
      | sumbool _ _ => destruct X
      | _ => destruct X eqn:?
      end
    end.

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

  Lemma eutt_ret_vis_abs : forall {U} e (k : U -> itree E R2) x,
    eutt RR (Ret x) (Vis e k) -> False.
  Proof.
   intros * abs; apply eqit_inv in abs; inv abs.
  Qed.

  Lemma eutt_vis_ret_abs : forall {U} e (k : U -> itree E R1) x,
    eutt RR (Vis e k) (Ret x) -> False.
  Proof.
   intros * abs; apply eqit_inv in abs; inv abs.
  Qed.

  Lemma eutt_ret_trigger_abs : forall {U} e (k : U -> itree E R2) x,
    eutt RR (Ret x) (x <- trigger e;; k x) -> False.
  Proof.
   intros * abs; apply eqit_inv in abs; inv abs.
  Qed.

  Lemma eutt_trigger_ret_abs : forall {U} e (k : U -> itree E R1) x,
    eutt RR (x <- trigger e;; k x) (Ret x) -> False.
  Proof.
   intros * abs; apply eqit_inv in abs; inv abs.
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

Section EquivSem.

  Notation step_op := Operational.step.

  (* Lifting the operational stepping over itrees to the syntax
     via representation *)
  Definition step_sem : term -> option action -> term -> Prop :=
    fun t1 ma t2 => step_ccs (model t1) ma (model t2).

  Notation "P '⊢' a '→sem' Q" := (step_sem P a Q) (at level 50).
  Notation "P '⊢' a '→op'  Q" := (step_op P a Q)  (at level 50).

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

  Definition head_of_action a :=
    match a with
    | Some a => HAct a
    | None => HSynch
    end.

  Lemma eqit_inv_Vis_Type {E X1 X2 R1 R2} (RR : R1 -> R2 -> Prop) (b1 b2: bool) (e1 : E X1) (e2: E X2) (k1 : X1 -> itree E R1) (k2 : X2 -> itree E R2)
        (EQ : eqit RR b1 b2 (Vis e1 k1) (Vis e2 k2)) : X1 = X2.
  Proof.
    punfold EQ; inv EQ.
    reflexivity.
  Qed.

  Lemma eqit_inv_event {E X R} (RR : R -> R -> Prop) (b1 b2: bool) (e1 e2 : E X) (k1 k2 : X -> itree E R)
        (EQ : eqit RR b1 b2 (Vis e1 k1) (Vis e2 k2)) : e1 = e2.
  Proof.
    punfold EQ; inv EQ.
    dependent destruction H4.
    reflexivity.
  Qed.

  Inductive Returns_legacy {E A} (a: A) : itree E A -> Prop :=
  | Returns_legacyRet: forall t, t ≈ Ret a -> Returns_legacy a t
  | Returns_legacyVis: forall {X} (e: E X) (x: X) t k,
      t ≈ Vis e k -> Returns_legacy a (k x) -> Returns_legacy a t.

  Global Instance Returns_legacy_eqit {E A} b hd :
    Proper (eqit eq b b ==> flip impl) (@Returns_legacy E A hd).
  Proof.
    do 4 red.
    intros * Eq Ret.
    revert b x Eq.
    induction Ret;
      intros;
      [ apply Returns_legacyRet | apply Returns_legacyVis with X e x k];
      case_eq b;
      intro;
      subst;
      now rewrite Eq || assumption.
  Qed.

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

  Inductive Finite {E X} R : itree E X -> Prop :=
  | FRet : forall t (x: X), eq_itree R t (Ret x) -> Finite R t
  | FTau : forall t P, eq_itree R t (Tau P) -> Finite R P -> Finite R t
  | FVis {A} : forall t (e: E A) k,
      eq_itree R t (Vis e k) -> (forall x, Finite R (k x)) -> Finite R t.

  Inductive FiniteSchedTree {X} R : itree ccsE X -> Prop :=
  | FSTRet : forall t (x: X), eq_itree R t (Ret x) -> FiniteSchedTree R t
  | FSTTau : forall t P, eq_itree R t (Tau P) -> FiniteSchedTree R P -> FiniteSchedTree R t
  | FSTPlus : forall t k,
      eq_itree R t (b <- trigger Plus;; k b) ->
      (forall b, FiniteSchedTree R (k b)) ->
      FiniteSchedTree R t
  | FSTSched2 : forall t k,
      eq_itree R t (b <- trigger Sched2;; k b) ->
      (forall b, FiniteSchedTree R (k b)) ->
      FiniteSchedTree R t
  | FSTSched3 : forall t k,
      eq_itree R t (c <- trigger Sched3;; k c) ->
      (forall c, FiniteSchedTree R (k c)) ->
      FiniteSchedTree R t.

  Global Instance Finite_cong {E X} :
    Proper (eq_itree eq ==> flip impl) (@Finite E X eq).
  Proof.
    do 4 red.
    intros x y Cong Fin.
    revert x Cong.
    induction Fin;
      intros.
    - apply FRet with x.
      now rewrite Cong.
    - apply FTau with P.
      + now rewrite Cong.
      + assumption.
    - apply FVis with A e k.
      + now rewrite Cong.
      + assumption.
  Qed.

  Global Instance FST_cong {X} :
    Proper (eq_itree eq ==> flip impl) (@FiniteSchedTree X eq).
  Proof.
    do 4 red.
    intros x y Cong Fin.
    revert x Cong.
    induction Fin;
      intros.
    - apply FSTRet with x.
      now rewrite Cong.
    - apply FSTTau with P.
      + now rewrite Cong.
      + assumption.
    - apply FSTPlus with k.
      + now rewrite Cong.
      + assumption.
    - apply FSTSched2 with k.
      + now rewrite Cong.
      + assumption.
    - apply FSTSched3 with k.
      + now rewrite Cong.
      + assumption.
  Qed.

  Definition eq_head R : head -> head -> Prop :=
    fun h1 h2 =>
      match h1,h2 with
      | HDone, HDone => True
      | HSynch t1, HSynch t2 => eq_itree R t1 t2
      | HAct a1 t1, HAct a2 t2 => a1 = a2 /\ eq_itree R t1 t2
      | _, _ => False
      end.
  Hint Unfold eq_head : core.

  Lemma eq_head_trans {R} :
    Transitive R -> Transitive (eq_head R).
  Proof.
    unfold Transitive.
    intros.
    induction x, y, z;
      cbn;
      try (reflexivity || contradiction).
    - unfold eq_head in *.
      eapply Transitive_eqit;
        eauto.
    - unfold eq_head in *.
      destruct H0, H1.
      split.
      + now rewrite H0.
      + eapply Transitive_eqit;
          eauto.
  Qed.

  Lemma eq_head_refl {R} :
    Reflexive R -> Reflexive (eq_head R).
  Proof.
    unfold Reflexive.
    induction x;
      cbn.
    - reflexivity.
    - now apply Reflexive_eqit.
    - split.
      + reflexivity.
      + now apply Reflexive_eqit.
  Qed.

  Global Instance get_hd_eq_itree {R} :
    Proper (eq_itree R ==> eq_itree (eq_head R)) get_hd.
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

  Global Instance Finite_eq_head {E} :
    Proper (eq_itree eq ==> flip impl) (@Finite E head (eq_head eq)).
  Proof.
    do 4 red.
    intros x y Cong Fin.
    revert x Cong.
    induction Fin;
      intros.
    - apply FRet with x.
      now rewrite Cong.
    - apply FTau with P.
      + now rewrite Cong.
      + assumption.
    - apply FVis with A e k.
      + now rewrite Cong.
      + assumption.
  Qed.

  Global Instance Finite_eq_itree_eq_head {E} :
    Proper (eq_itree (eq_head eq) ==> flip impl) (@Finite E head (eq_head eq)).
  Proof.
    do 4 red.
    intros x y Cong Fin.
    revert x Cong.
    induction Fin;
      intros.
    - apply FRet with x.
      eapply Transitive_eqit.
      apply eq_head_trans, eq_Transitive.
      + apply Cong.
      + apply H.
    - apply FTau with P.
      + eapply Transitive_eqit.
        apply eq_head_trans, eq_Transitive.
        * apply Cong.
        * apply H.
      + assumption.
    - apply FVis with A e k.
      + eapply Transitive_eqit.
        apply eq_head_trans, eq_Transitive.
        * apply Cong.
        * apply H.
      + assumption.
  Qed.

  Global Instance FST_eq_head :
    Proper (eq_itree eq ==> flip impl) (FiniteSchedTree (eq_head eq)).
  Proof.
    do 4 red.
    intros * Cong FST.
    revert Cong.
    induction FST;
      intros.
    - apply FSTRet with x0.
      now rewrite Cong.
    - apply FSTTau with P.
      + now rewrite Cong.
      + assumption.
    - eapply FSTPlus.
      + rewrite Cong.
        apply H.
      + assumption.
    - eapply FSTSched2.
      + rewrite Cong.
        apply H.
      + assumption.
    - eapply FSTSched3.
      + rewrite Cong.
        apply H.
      + assumption.
  Qed.

  Global Instance FST_eq_itree_eq_head :
    Proper (eq_itree (eq_head eq) ==> flip impl) (FiniteSchedTree (eq_head eq)).
  Proof.
    do 4 red.
    intros * Cong FST.
    revert Cong.
    induction FST;
      intros.
    - apply FSTRet with x0.
      eapply Transitive_eqit.
      apply eq_head_trans, eq_Transitive.
      + apply Cong.
      + apply H.
    - apply FSTTau with P.
      + eapply Transitive_eqit.
        apply eq_head_trans, eq_Transitive.
        * apply Cong.
        * apply H.
      + assumption.
    - eapply FSTPlus.
      + eapply Transitive_eqit.
        apply eq_head_trans, eq_Transitive.
        * apply Cong.
        * apply H.
      + assumption.
    - eapply FSTSched2.
      + eapply Transitive_eqit.
        apply eq_head_trans, eq_Transitive.
        * apply Cong.
        * apply H.
      + assumption.
    - eapply FSTSched3.
      + eapply Transitive_eqit.
        apply eq_head_trans, eq_Transitive.
        * apply Cong.
        * apply H.
      + assumption.
  Qed.

  (* TODO: is this lemma really useful? *)
  Lemma step_cong : forall t u v a,
      t ≅ u ->
      t ⊢ a →ccs v ->
      u ⊢ a →ccs v.
  Proof.
    intros * Cong Step.
    revert Cong.
    induction Step;
      intros;
      try rewrite <- Cong.
    - now constructor.
    - now constructor.
    - now apply S_Plus_L with L R.
    - now apply S_Plus_R with L R.
    - now apply S_Sched2_L with L R.
    - now apply S_Sched2_R with L R.
    - now apply S_Sched3_L with L R S.
    - now apply S_Sched3_R with L R S.
    - now apply S_Sched3_S with L R S.
  Qed.

  (* the next three lemmas seem to be the useful versions of the one above *)
  Lemma plus_can_step {X} : forall k (k': X -> ccs) a b q,
      (hd <- k b;; k' hd) ⊢ a →ccs q ->
      vis Plus (fun x => (hd <- k x;; k' hd)) ⊢ a →ccs q.
  Proof.
    intros.
    case_eq b; intro.
    - apply S_Plus_L with
          (hd <- k true;; k' hd)
          (hd <- k false;; k' hd).
      + now rewrite H0 in H.
      + unfold plus.
        rewrite bind_trigger.
        apply eqit_Vis.
        intro.
        case_eq u;
          reflexivity.
    - apply S_Plus_R with
          (hd <- k true;; k' hd)
          (hd <- k false;; k' hd).
      + now rewrite H0 in H.
      + unfold plus.
        rewrite bind_trigger.
        apply eqit_Vis.
        intro.
        case_eq u;
          reflexivity.
  Qed.

  Lemma sched2_can_step {X} : forall k (k': X -> ccs) a b q,
      (hd <- k b;; k' hd) ⊢ a →ccs q ->
      vis Sched2 (fun x => (hd <- k x;; k' hd)) ⊢ a →ccs q.
  Proof.
    intros.
    case_eq b; intro.
    - apply S_Sched2_L with
          (hd <- k true;; k' hd)
          (hd <- k false;; k' hd).
      + now rewrite H0 in H.
      + unfold branch2.
        rewrite bind_trigger.
        apply eqit_Vis.
        intro.
        case_eq u;
          reflexivity.
    - apply S_Sched2_R with
          (hd <- k true;; k' hd)
          (hd <- k false;; k' hd).
      + now rewrite H0 in H.
      + unfold branch2.
        rewrite bind_trigger.
        apply eqit_Vis.
        intro.
        case_eq u;
          reflexivity.
  Qed.

  Lemma sched3_can_step {X} : forall k (k': X -> ccs) a b q,
      (hd <- k b;; k' hd) ⊢ a →ccs q ->
      vis Sched3 (fun x => (hd <- k x;; k' hd)) ⊢ a →ccs q.
  Proof.
    intros.
    case_eq b; intro.
    - apply S_Sched3_L with
          (hd <- k Left;; k' hd)
          (hd <- k Right;; k' hd)
          (hd <- k Synchronize;; k' hd).
      + now rewrite H0 in H.
      + unfold branch3.
        rewrite bind_trigger.
        apply eqit_Vis.
        intro.
        case_eq u;
          reflexivity.
    - apply S_Sched3_R with
          (hd <- k Left;; k' hd)
          (hd <- k Right;; k' hd)
          (hd <- k Synchronize;; k' hd).
      + now rewrite H0 in H.
      + unfold branch3.
        rewrite bind_trigger.
        apply eqit_Vis.
        intro.
        case_eq u;
          reflexivity.
    - apply S_Sched3_S with
          (hd <- k Left;; k' hd)
          (hd <- k Right;; k' hd)
          (hd <- k Synchronize;; k' hd).
      + now rewrite H0 in H.
      + unfold branch3.
        rewrite bind_trigger.
        apply eqit_Vis.
        intro.
        case_eq u;
          reflexivity.
  Qed.

  Lemma step_ccs_through_FST :
    forall (t : ccsT head) (k : head -> ccs) (q : ccs) a hd,
      FiniteSchedTree (eq_head eq) t ->
      Returns_legacy hd t ->
      k hd ⊢ a →ccs q ->
      (x <- t;; k x) ⊢ a →ccs q.
  Proof.
    intros * FST.
    revert k q a hd.
    induction FST;
      intros * Ret Step.
    - inversion Ret; subst.
      + now rewrite H0, bind_ret_l.
      + apply eq_sub_eutt in H.
        rewrite H0 in H.
        now apply eutt_vis_ret_abs in H.
    - inversion Ret; subst.
      + now rewrite H0, bind_ret_l.
      + assert (t ≅ Tau P). admit. (* could H be used here? *)
        rewrite H2, tau_eutt.
        apply IHFST with hd.
        * apply eq_sub_eutt in H2.
          rewrite tau_eutt in H2.
          now rewrite <- H2.
        * assumption.
    - inversion Ret;
        subst.
      + now rewrite H2, bind_ret_l.
      + rewrite H2, bind_vis.
        apply eq_sub_eutt in H.
        rewrite bind_trigger, H2 in H.
        apply eqit_inv_Vis_Type in H as H4; subst.
        apply eqit_inv_event in H as H4; subst.
        apply plus_can_step with x.
        apply eqit_inv_Vis with (u := x) in H.
        assert (forall x, k1 x ≈ k x). admit. (* could H be used here? *)
        rewrite H4.
        apply H1 with hd.
        * now rewrite <- H4.
        * assumption.
    - inversion Ret;
        subst.
      + apply eq_sub_eutt in H.
        rewrite H2 in H.
        now apply eutt_ret_trigger_abs in H.
      + rewrite H2, bind_vis.
        apply eq_sub_eutt in H.
        rewrite bind_trigger, H2 in H.
        apply eqit_inv_Vis_Type in H as H4; subst.
        apply eqit_inv_event in H as H4; subst.
        apply sched2_can_step with x.
        apply eqit_inv_Vis with (u := x) in H.
        assert (forall x, k1 x ≈ k x). admit. (* could H be used here? *)
        rewrite H4.
        apply H1 with hd.
        * now rewrite <- H4.
        * assumption.
    - inversion Ret;
        subst.
      + apply eq_sub_eutt in H.
        rewrite H2 in H.
        now apply eutt_ret_trigger_abs in H.
      + rewrite H2, bind_vis.
        apply eq_sub_eutt in H.
        rewrite bind_trigger, H2 in H.
        apply eqit_inv_Vis_Type in H as H4; subst.
        apply eqit_inv_event in H as H4; subst.
        apply sched3_can_step with x.
        apply eqit_inv_Vis with (u := x) in H.
        assert (forall x, k1 x ≈ k x). admit. (* could H be used here? *)
        rewrite H4.
        apply H1 with hd.
        * now rewrite <- H4.
        * assumption.
  Admitted.

  Lemma step_ccs_through_FST_weak :
    forall (t : ccsT head) (k : head -> ccs) (q : ccs) a,
      FiniteSchedTree (eq_head eq) t ->
      (forall hd, k hd ⊢ a →ccs q) ->
      (hd <- t;; k hd) ⊢ a →ccs q.
  Proof.
    intros * FST Step.
    revert k q a Step.
    assert (forall (x: ccsT head) y, eq_itree (eq_head eq) x y -> x ≅ y) as Cheat. admit.
    induction FST;
      intros;
      apply Cheat in H;
      clear Cheat;
      rewrite H.
    - now rewrite bind_ret_l.
    - rewrite tau_eutt.
      now apply IHFST.
    - rewrite bind_trigger, bind_vis.
      (* For some reason we have to choose a boolean here...? *)
      apply plus_can_step with true.
      now apply H1.
    - rewrite bind_trigger, bind_vis.
      apply sched2_can_step with true.
      now apply H1.
    - rewrite bind_trigger, bind_vis.
      apply sched3_can_step with Left.
      now apply H1.
  Admitted.

  Lemma step_ccs_is_returned_by_get_hd :
    forall (p q : ccs) a,
      p ⊢ a →ccs q ->
      Returns_legacy (head_of_action a q) (get_hd p).
  Proof.
    intros.
    induction H.
    - pose proof (get_hd_unfold (act a;; P)) as Eq;
        revert Eq;
        cbn;
        ITree.fold_subst;
        intro.
      apply Returns_legacyRet.
      (* since the right part of Eq is (Ret tt;; P) maybe it's not
         a ≅ we want but a ≈ ? *)
  Admitted.

  Lemma finite_head : forall P,
      Finite eq P ->
      FiniteSchedTree (eq_head eq) (get_hd P).
  Proof.
    intros * Fin.
    induction Fin.
    - (* Ret *)
      pose proof (get_hd_unfold (Ret x)) as Eq;
        cbn in Eq.
      apply FSTRet with HDone.
      apply get_hd_eq_itree in H.
      now rewrite Eq in H.
    - (* Tau *)
      pose proof (get_hd_unfold (Tau P)) as Eq;
        cbn in Eq.
      apply FST_eq_itree_eq_head with (get_hd (Tau P)).
      + now apply get_hd_eq_itree in H.
      + rewrite Eq.
        apply FSTTau with (get_hd P).
        * apply Reflexive_eqit, eq_head_refl, eq_Reflexive.
        * assumption.
    - (* Vis *)
      apply FST_eq_itree_eq_head with (get_hd (Vis e k)).
      + now apply get_hd_eq_itree in H.
      + rewrite get_hd_unfold; cbn.
        break_match_goal.
        * (* Vis NonDetE, special case *)
          induction n;
            [ apply FSTPlus with (fun x => get_hd (k x))
            | apply FSTSched2 with (fun x => get_hd (k x))
            | apply FSTSched3 with (fun x => get_hd (k x))];
            (rewrite bind_trigger || assumption);
            apply Reflexive_eqit, eq_head_refl, eq_Reflexive.
        * (* Vis anything else *)
          repeat break_match_goal;
            eapply FSTRet;
            apply Reflexive_eqit, eq_head_refl, eq_Reflexive.
  Qed.

  Lemma finite_bind {E X Y} : forall (t: itree E Y) (k: Y -> itree E X),
      Finite eq t -> (forall y, Finite eq (k y)) -> Finite eq (y <- t;; k y).
  Proof.
    intros * Fin.
    induction Fin;
      intro FinK.
    - apply eqitree_inv_Ret_r in H as [r' [_ Eq]].
      now rewrite unfold_bind, Eq.
    - apply eqitree_inv_Tau_r in H as [t' [Eq Rel]].
      rewrite unfold_bind, Eq.
      eapply FTau.
      + reflexivity.
      + apply IHFin in FinK.
        now rewrite Rel.
    - apply eqitree_inv_Vis_r in H as [k' [Eq Rel]].
      rewrite unfold_bind, Eq.
      eapply FVis.
      + reflexivity.
      + cbn.
        intros.
        apply H1 with x in FinK.
        now rewrite Rel.
  Qed.

  Lemma finite_bind' {E X} : forall t (k: head -> itree E X),
      Finite (eq_head eq) t -> (forall y, Finite eq (k y)) -> Finite eq (y <- t;; k y).
  Proof.
    intros * Fin.
    revert X k.
    induction Fin;
      intros * FinK.
    - (* Ret *)
      apply eqitree_inv_Ret_r in H as [r [_ Eq]].
      rewrite unfold_bind, Eq.
      apply FinK.
    - (* Tau *)
      apply eqitree_inv_Tau_r in H as [P' [Eq R]].
      rewrite unfold_bind, Eq.
      apply FTau with (y <- P';; k y).
      + reflexivity.
      + apply IHFin in FinK as FinP.
        (* rewrite R *)
        admit.
    - (* Vis *)
      apply eqitree_inv_Vis_r in H as [k' [Eq Rel]].
      rewrite unfold_bind, Eq.
      apply FVis with A e (fun x : A => y <- k' x;; k0 y).
      + reflexivity.
      + intro.
        apply (H1 x) in FinK.
        (* now rewrite Rel. *)
        admit.
  Admitted.

  Lemma FST_means_Finite {X} : forall (P: ccsT X) R,
      FiniteSchedTree R P -> Finite R P.
  Proof.
    intros.
    induction H.
    - now apply FRet with x.
    - now apply FTau with P.
    - rewrite bind_trigger in H.
      eapply FVis;
        eauto.
    - rewrite bind_trigger in H.
      eapply FVis;
        eauto.
    - rewrite bind_trigger in H.
      eapply FVis;
        eauto.
  Qed.

  Lemma finite_interp {E F X} : forall (h : Handler E F) (t : itree E X),
      Finite eq t ->
      (forall Y (e : E Y), Finite eq (h _ e)) ->
      Finite eq (interp h t).
  Proof.
    intros h t FinT.
    revert h.
    induction FinT;
      intros.
    - apply eqitree_inv_Ret_r in H as [r' [_ Eq]].
      rewrite unfold_interp;
        unfold _interp;
        rewrite Eq.
      now apply FRet with r'.
    - apply eqitree_inv_Tau_r in H as [t' [Eq Rel]].
      rewrite unfold_interp;
        unfold _interp;
        rewrite Eq.
      apply FTau with (interp h t').
      + reflexivity.
      + apply IHFinT in H0.
        now rewrite Rel.
    - apply eqitree_inv_Vis_r in H as [k' [Eq Rel]].
      rewrite unfold_interp;
        unfold _interp;
        rewrite Eq.
      apply finite_bind.
      + apply H2.
      + intro.
        apply FTau with (interp h (k' y)).
        * reflexivity.
        * apply H1 with (x := y) in H2.
          now rewrite Rel.
  Qed.

  Lemma finite_restrict {Y}: forall c (e: ccsE Y),
      Finite eq (h_restrict c Y e).
  Proof.
    intros.
    destruct e as [[ |  | ] | [[?] | [? | ?]]];
      cbn;
      unfold h_trigger, trigger.
    4: { destruct a;
         case_eq (c =? c0)%string;
         intro;
         try (unfold dead;
              rewrite bind_trigger);
         eapply FVis.
         1,3,5,7: reflexivity.
         all: intro;
           ( now apply FRet with x || induction x). }
    all: eapply FVis.
    1,3,5,7,9: reflexivity.
    all: intro;
      now apply FRet with x.
  Qed.

  (* In order to prove that : [forall P, finite (model P)],
     we need to reason about the co-recursive call performed by para.
     However, this call does not take place on immediately structurally smaller
     arguments, whether on the syntactic level via model nor on the trees themselves.
     One sensible first step is to introduce an intermediate result on [para]:
     [forall t s, Finite t -> Finite s -> Finite (para t s)]
     As mentionned above however, this is still not the panacea: [Finite] essentially
     gives structural induction on your tree, but the call is still not structural.
     Hence we probably need to introduce the size of finite trees and proceed by
     strong induction on the sum of the sizes of both trees, which requires quite
     a bit of boilerplate and work.
   *)

  Lemma finite_para : forall P Q,
      Finite eq P -> Finite eq Q -> Finite eq (para P Q).
  Proof.
    intros.
    rewrite para_unfold.
    apply finite_bind'.
    1: {apply FST_means_Finite.
        now apply finite_head. }
    intro rP.
    apply finite_bind'.
    1: {apply FST_means_Finite.
        now apply finite_head. }
    intro rQ.
    destruct rP, rQ.
    - now apply FRet with tt.
    - eapply FVis.
      reflexivity.
      intro; cbn.
      admit.
    - eapply FVis.
      reflexivity.
      intro; cbn.
      admit.
    - eapply FVis.
      reflexivity.
      intro; cbn.
      admit.
    - unfold branch2.
      rewrite bind_trigger.
      eapply FVis.
      reflexivity.
      intro; cbn.
      case_eq x; intro; subst.
      + eapply FVis.
        reflexivity.
        intros []; cbn.
        admit.
      + eapply FVis.
        reflexivity.
        intros []; cbn.
        admit.
    - unfold branch2.
      rewrite bind_trigger.
      eapply FVis.
      reflexivity.
      intro; cbn.
      case_eq x; intro; subst.
      + eapply FVis.
        reflexivity.
        intros []; cbn.
        admit.
      + eapply FVis.
        reflexivity.
        intros []; cbn.
        admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma finite_model : forall (P : term),
      Finite eq ⟦P⟧.
  Proof.
    induction P;
      cbn.
    - (* 0 *)
      unfold done.
      now apply FRet with tt.
    - (* a ⋅ P *)
      unfold act.
      rewrite bind_trigger.
      now eapply FVis.
    - (* para *)
      now apply finite_para.
    - (* plus *)
      unfold plus.
      rewrite bind_trigger.
      eapply FVis.
      reflexivity.
      intro.
      case_eq x; auto.
    - (* restrict *)
      apply finite_interp.
      assumption.
      intros.
      apply finite_restrict.
  Qed.


  Lemma op_involutive : forall a, op (op a) = a.
  Proof.
    intros []; reflexivity.
  Qed.

  Lemma SumL_sem :
    forall P a Q P',
      P ⊢a→sem P' ->
      P ⊕ Q ⊢a→sem P'.
  Proof.
    intros.
    apply S_Plus_L with ⟦P⟧ ⟦Q⟧; auto; reflexivity.
  Qed.

  Lemma SumR_sem :
    forall P a Q Q',
      Q ⊢a→sem Q' ->
      P ⊕ Q ⊢a→sem Q'.
  Proof.
    intros.
    apply S_Plus_R with ⟦P⟧ ⟦Q⟧; auto; reflexivity.
  Qed.

 Lemma ParL_sem :
    forall P a Q P',
      P ⊢a→sem P' ->
      P ∥ Q ⊢a→sem P' ∥ Q.
  Proof.
    intros * STEP.
    unfold step_sem in *.
    cbn.
    rewrite para_unfold.
    apply step_ccs_through_FST with (head_of_action a ⟦P'⟧).
    3:apply step_ccs_through_FST_weak.
    * apply finite_head, finite_model.
    * apply step_ccs_is_returned_by_get_hd; assumption.
    * apply finite_head, finite_model.
    * intros hd.
      destruct hd eqn:EQHD, a eqn:EQa; cbn;
        try (constructor; unfold act,synch; rewrite bind_trigger; reflexivity);
        try (eapply S_Sched2_L; [constructor; unfold act,synch; rewrite bind_trigger; reflexivity | reflexivity]).
        destruct (are_opposite a1 a0).
        eapply S_Sched3_L; [constructor; unfold act; rewrite bind_trigger; reflexivity | reflexivity].
        eapply S_Sched2_L; [constructor; unfold act; rewrite bind_trigger; reflexivity | reflexivity].
  Qed.

  Lemma ParR_sem :
    forall P a Q Q',
      Q ⊢a→sem Q' ->
      P ∥ Q ⊢a→sem P ∥ Q'.
  Proof.
    intros * STEP.
    unfold step_sem in *.
    cbn.
    rewrite para_unfold.
    apply step_ccs_through_FST_weak.
    2:intros; apply step_ccs_through_FST with (head_of_action a ⟦Q'⟧).
    * apply finite_head, finite_model.
    * apply finite_head, finite_model.
    * apply step_ccs_is_returned_by_get_hd; assumption.
    * destruct hd eqn:EQHD, a eqn:EQa; cbn;
        try (constructor; unfold act,synch; rewrite bind_trigger; reflexivity);
        try (eapply S_Sched2_R; [constructor; unfold act,synch; rewrite bind_trigger; reflexivity | reflexivity]).
        destruct (are_opposite a0 a1).
        eapply S_Sched3_R; [constructor; unfold act,synch; rewrite bind_trigger; reflexivity | reflexivity].
        eapply S_Sched2_R; [constructor; unfold act,synch; rewrite bind_trigger; reflexivity | reflexivity].
  Qed.

  Lemma ParS_sem :
    forall P a Q P' Q',
      P ⊢Some a→sem P' ->
      Q ⊢Some (op a)→sem Q' ->
      P ∥ Q ⊢None→sem P' ∥ Q'.
  Proof.
    intros * STEP_P STEP_Q.
    unfold step_sem in *.
    cbn.
    rewrite para_unfold.
    apply step_ccs_through_FST with (head_of_action (Some a) ⟦P'⟧).
    3:apply step_ccs_through_FST with (head_of_action (Some (op a)) ⟦Q'⟧).
    * apply finite_head, finite_model.
    * apply step_ccs_is_returned_by_get_hd; assumption.
    * apply finite_head, finite_model.
    * apply step_ccs_is_returned_by_get_hd; assumption.
    * cbn.
      unfold are_opposite.
      rewrite op_involutive, eqb_action_refl.
      eapply S_Sched3_S; [constructor; unfold synch; rewrite bind_trigger; reflexivity | reflexivity].
  Qed.

  #[global] Instance restrict_eq_itree c :
      Proper (eq_itree eq ==> eq_itree eq) (restrict c).
  Proof.
    unfold restrict; do 2 red; intros * EQ; rewrite EQ; reflexivity.
  Qed.

  #[global] Instance restrict_eutt c :
      Proper (eutt eq ==> eutt eq) (restrict c).
  Proof.
    unfold restrict; do 2 red; intros * EQ; rewrite EQ; reflexivity.
  Qed.

  Lemma restrict_tau : forall c P,
    restrict c (Tau P) ≅ Tau (restrict c P).
  Proof.
    unfold restrict; intros; rewrite interp_tau; reflexivity.
  Qed.

  Lemma restrict_act : forall c P a,
    use_channel c (Some a) = false ->
    restrict c (act a;; P) ≈ act a;; restrict c P.
  Proof.
    unfold restrict, act; intros * NEQ.
    rewrite interp_bind, interp_trigger.
    cbn in *; destruct a; rewrite NEQ; reflexivity.
  Qed.

  Lemma restrict_synch : forall c P,
    use_channel c None = false ->
    restrict c (synch;; P) ≈ synch;; restrict c P.
  Proof.
    unfold restrict, synch; intros * NEQ.
    rewrite interp_bind, interp_trigger.
    reflexivity.
  Qed.

  Lemma restrict_plus : forall c L R,
    restrict c (plus L R) ≈ plus (restrict c L) (restrict c R).
  Proof.
    unfold restrict, plus; intros *.
    rewrite interp_bind, interp_trigger.
    cbn.
    apply eutt_eq_bind; intros []; reflexivity.
  Qed.

  Lemma restrict_branch2 : forall c L R,
    restrict c (branch2 L R) ≈ branch2 (restrict c L) (restrict c R).
  Proof.
    unfold restrict, branch2; intros *.
    rewrite interp_bind, interp_trigger.
    cbn.
    apply eutt_eq_bind; intros []; reflexivity.
  Qed.

  Lemma restrict_branch3 : forall c L R S,
    restrict c (branch3 L R S) ≈ branch3 (restrict c L) (restrict c R) (restrict c S).
  Proof.
    unfold restrict, branch3; intros *.
    rewrite interp_bind, interp_trigger.
    cbn.
    apply eutt_eq_bind; intros []; reflexivity.
  Qed.

  Lemma Restrict_sem_aux :
    forall P a c P',
      use_channel c a = false ->
      P ⊢a→ccs P' ->
      restrict c P ⊢a→ccs restrict c P'.
  Proof.
    intros * NEQ STEP.
    induction STEP; rewrite H.
    - rewrite restrict_act; auto.
      constructor; reflexivity.
    - rewrite restrict_synch; auto.
      constructor; reflexivity.
    - rewrite restrict_plus.
      eapply S_Plus_L; eauto.
      reflexivity.
    - rewrite restrict_plus.
      eapply S_Plus_R; eauto.
      reflexivity.
    - rewrite restrict_branch2.
      eapply S_Sched2_L; [| reflexivity].
      eauto.
    - rewrite restrict_branch2.
      eapply S_Sched2_R; [| reflexivity].
      eauto.
    - rewrite restrict_branch3.
      eapply S_Sched3_L; [| reflexivity].
      eauto.
    - rewrite restrict_branch3.
      eapply S_Sched3_R; [| reflexivity].
      eauto.
    - rewrite restrict_branch3.
      eapply S_Sched3_S; [| reflexivity].
      eauto.
  Qed.

  Lemma Restrict_sem :
    forall P a c P',
      use_channel c a = false ->
      P ⊢a→sem P' ->
      P ∖ c ⊢a→sem P' ∖ c.
  Proof.
    intros * NEQ STEP.
    apply Restrict_sem_aux; auto.
  Qed.

  Theorem model_complete :
    forall P a Q,
      P ⊢a→op Q ->
      P ⊢a→sem Q.
  Proof.
    intros * StepOp.
    (* Lock-step simulation *)
    induction StepOp.
    + now constructor.
    + now apply SumL_sem.
    + now apply SumR_sem.
    + now apply ParL_sem.
    + now apply ParR_sem.
    + eapply ParS_sem; eassumption.
    + now apply Restrict_sem.
  Qed.

  Definition stuck_ccs P := forall a Q, ~ P ⊢a→ccs Q.

  Lemma done_cannot_step : stuck_ccs done.
  Proof.
    red; unfold done; intros * STEP.
    inv STEP.
    all: match goal with
         | h : eutt _ (Ret _) _ |- _ =>
           eapply eutt_ret_trigger_abs, h
         end.
  Qed.

  Ltac abs_eutt H := apply eqit_inv in H; inv H.
  Ltac is_abs :=
    match goal with
    | h : eutt _ _ _ |- _ => abs_eutt h
    end.

  (* Makes the canonization super-inefficient, might want to compute the liste of bound variables in one pass *)
  Fixpoint use_channel_term (P : term) (c : chan) : bool :=
    match P with
    | 0 => false
    | ↑ c' ⋅ P => (c =? c')%string || use_channel_term P c
    | ↓ c' ⋅ P => (c =? c')%string || use_channel_term P c
    | P ⊕ Q | P ∥ Q => use_channel_term P c || use_channel_term Q c
    | P ∖ c' => use_channel_term P c
    end.
  Notation "c ∈ P" := (use_channel_term P c = true) (at level 80).
  Notation "c ∉ P" := (use_channel_term P c = false) (at level 80).

  Fixpoint canonize (P : term) : term :=
    match P with
    | 0 => 0
    | a ⋅ P => a ⋅ (canonize P)
    | P ⊕ Q => canonize P ⊕ canonize Q
    | P ∥ Q => canonize P ∥ canonize Q
    | P ∖ c => if use_channel_term P c then canonize P ∖ c else canonize P
    end
  .

  Lemma restrict_done : forall c,
    restrict c done ≈ done.
  Proof.
    intros; unfold restrict, done at 1; rewrite interp_ret; reflexivity.
  Qed.

  Lemma fresh_channel_act : forall c a P,
    c ∉ a ⋅ P ->
    use_channel c (Some a) = false /\ c ∉ P.
  Proof.
    cbn; intros * H; break_match_hyp H; subst; auto.
    apply Bool.orb_false_elim in H; apply H.
    apply Bool.orb_false_elim in H; apply H.
  Qed.

  Lemma fresh_channel_para : forall c P Q,
    c ∉ P ∥ Q ->
    c ∉ P /\ c ∉ Q.
  Proof.
    cbn; intros * H; apply Bool.orb_false_elim in H; apply H.
  Qed.

  Definition eutt_head R : head -> head -> Prop :=
    fun h1 h2 =>
      match h1,h2 with
      | HDone, HDone => True
      | HSynch t1, HSynch t2 => eutt R t1 t2
      | HAct a1 t1, HAct a2 t2 => a1 = a2 /\ eutt R t1 t2
      | _, _ => False
      end.
  Hint Unfold eutt_head : core.

  Global Instance get_hd_eutt :
    forall R,
      Proper (eutt R ==> eutt (eutt_head R)) get_hd.
  Proof.
    intros R; do 2 red.
    einit.
    ecofix CIH.
    intros * EQ.
    punfold EQ.
    setoid_rewrite get_hd_unfold.
    induction EQ; try inv CHECK.
    - estep; constructor; reflexivity.
    - estep; pclearbot. constructor; auto with paco.
    - pclearbot.
      destruct e as [? | [? | [? | ?]]].
      + estep; intros ?; ebase.
      + destruct a; estep.
      + destruct s; estep.
      + estep.
    - rewrite tau_euttge.
      rewrite get_hd_unfold.
      apply IHEQ.
    - rewrite tau_euttge.
      rewrite get_hd_unfold.
      apply IHEQ.
  Qed.

  Lemma restrict_para : forall c P Q,
    restrict c (para P Q) ≈ para (restrict c P) (restrict c Q).
  Proof.
  Admitted.

  (* TODO Actually curate some utils *)
  Ltac break_and :=
    match goal with
    | h : _ /\ _ |- _ => destruct h
    end.

  (* TODO Move to itrees *)
  Lemma euttG_trigger :
    forall {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
      (rH rL : itree E R1 -> itree E R2 -> Prop)
      (gL : forall x : itree E R1, (fun _ : itree E R1 => itree E R2) x -> Prop)
      (gH : itree E R1 -> itree E R2 -> Prop) (u : Type)
      (e : E u) (k1 : u -> itree E R1) (k2 : u -> itree E R2),
    (forall v : u, euttG RR gH gH gH gH (k1 v) (k2 v)) ->
    euttG RR rH rL gL gH (x <- trigger e;; k1 x) (x <- trigger e;; k2 x).
  Proof.
    intros.
    rewrite 2 bind_trigger.
    apply euttG_vis; auto.
  Qed.

  Ltac etrigger :=
     repeat red; under_forall ltac:(eapply euttG_trigger; eauto with paco).

  #[global] Instance para_eutt :
    Proper (eutt eq ==> eutt eq ==> eutt eq) para.
  Proof.
    do 3 red.
    einit; ecofix CIH.
    intros P P' EQP Q Q' EQQ.
    rewrite 2 para_unfold.
    ebind; econstructor.
    apply get_hd_eutt with (R := eq); auto.
    intros uP1 uP2 EQHP.
    ebind; econstructor.
    apply get_hd_eutt with (R := eq); auto.
    intros uQ1 uQ2 EQHQ.
    destruct uP1, uP2; cbn in EQHP; try now inversion EQHP; repeat break_and; subst.
    all: destruct uQ1, uQ2; cbn in EQHQ; try (now inversion EQHQ); repeat break_and; subst.
    all: try estep.
    all: try (unfold branch2; etrigger; intros []; estep).
    break_match_goal.
    unfold branch3; etrigger; intros []; estep.
    unfold branch2; etrigger; intros []; estep.
  Qed.

  #[global] Instance plus_eutt :
    Proper (eutt eq ==> eutt eq ==> eutt eq) plus.
  Proof.
    intros P P' EQP Q Q' EQQ.
    unfold plus; apply eutt_eq_bind; intros []; auto.
  Qed.

  Lemma restrict_dead : forall c,
      restrict c dead ≈ dead.
  Proof.
    intros; unfold restrict, dead.
    rewrite interp_bind, interp_trigger.
    cbn; unfold h_trigger.
    apply eutt_eq_bind; intros [].
  Qed.

  Lemma restrict_dead' : forall c,
      interp (h_restrict c) (@dead unit _ _) ≈ dead.
  Proof.
    apply restrict_dead.
  Qed.

  Lemma restrict_commut : forall P c c',
    restrict c (restrict c' P) ≈ restrict c' (restrict c P).
  Proof.
    intros; revert P.
    einit.
    ecofix CIH.
    intros P.
    rewrite (itree_eta P).
    unfold restrict.
    destruct (observe P).
    - rewrite !interp_ret; eret.
    - rewrite !interp_tau; etau.
    - rewrite !interp_vis, !interp_bind.
      ebind; apply pbc_intro_h with eq.
      + destruct e as [| [| []]]; cbn; unfold h_trigger; cbn.
        all: try (rewrite !interp_trigger; cbn;unfold h_trigger; cbn; reflexivity).
        destruct a; cbn; repeat break_match_goal; cbn.
        all: rewrite ?restrict_dead',?interp_trigger; cbn; rewrite ?Heqb,?Heqb0; reflexivity.
      + intros ? ? ->.
        rewrite !interp_tau.
        etau.
  Qed.

  Lemma restrict_unused_channel : forall P c,
    c ∉ P ->
    ⟦P ∖ c⟧ ≈ ⟦P⟧.
  Proof.
    intros *; induction P; intros NIN.
    - apply restrict_done.
    - apply fresh_channel_act in NIN as [? ?].
      cbn; rewrite restrict_act; auto.
      apply eutt_eq_bind; intros []; auto.
    - cbn in *. rewrite restrict_para; auto.
      apply fresh_channel_para in NIN as []; rewrite IHP1,IHP2; auto.
      reflexivity.
    - cbn in *. rewrite restrict_plus; auto.
      apply fresh_channel_para in NIN as []; rewrite IHP1,IHP2; auto.
      reflexivity.
    - cbn in *.
      rewrite restrict_commut, IHP; auto.
      reflexivity.
  Qed.

  Lemma canonize_equivalence_class :
    forall P Q,
      ⟦P⟧ ≈ ⟦Q⟧ <-> canonize P = canonize Q.
  Proof.
    intros *; split; intros EQ.
    - admit.
    - revert Q EQ.
      induction P; cbn.
      + induction Q; intros EQ; try now inversion EQ.
        cbn in EQ.
        break_match_hyp EQ; [inv EQ |].
        rewrite IHQ; auto.
        symmetry; apply restrict_unused_channel; auto.
      + induction Q; cbn; intros EQ; try now inversion EQ.
        inv EQ.
        apply eutt_eq_bind; intros []; auto.
        break_match_hyp EQ; [inv EQ |].
        rewrite IHQ; auto.
        symmetry; apply restrict_unused_channel; auto.
      + induction Q; cbn; intros EQ; try now inversion EQ.
        inv EQ.
  Abort.

  Lemma act_sem_inv : forall a b P Q,
    a ⋅ P ⊢b→sem Q ->
    canonize Q = canonize P /\ b = Some a.
  Proof.
  Abort.

  Theorem model_correct :
    forall P a Q,
      P ⊢a→sem Q ->
      P ⊢a→op Q.
  Proof.
    induction P; intros * STEP.
    - red in STEP.
      exfalso; eapply done_cannot_step; eauto.
    - red in STEP.
      cbn in STEP.
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
      apply model_complete; auto.

    - (* The operational side can simulate the denotational semantics *)
      intros a P' StepSem.
      exists P'; split; [| auto].
      apply model_correct; auto.

  Qed.

  (* BEGIN PROOFS IN PROGRESS FOR THE ADMITTED LEMMAS ABOVE *)

  Theorem get_hd_means_step_deprecated : forall P a P',
      Returns_legacy (head_of_action a P') (get_hd P)
      <->
      step_ccs P a P'.
  Proof.
    split; intros.
    - (* Returns -> step :
       * if a finite path exists in the [get_hd] tree, it
       * can be used as a proof tree to justify a [step_ccs] *)
      remember (head_of_action a P') as aP'.
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
  (*
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
    + admit. *)
  Admitted.

  Theorem get_hd_always_returns : forall P, exists a k, Returns (head_of_action a k) (get_hd (model P)).
  Proof.
    induction P.
    - simpl.
  Admitted.

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

  Set Nested Proofs Allowed.

End EquivSem.
