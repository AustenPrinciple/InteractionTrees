(* begin hide *)
From ITree Require Import
     ITree
     Eq.Eq
     Events.Exception
     ITreeFacts.

Require Import PropT.
Import ITreeNotations.
Open Scope itree.

From Coq Require Import
     List
     Strings.String.

(* end hide *)

Open Scope string.

Section Syntax.

  Definition chan : Set := string.
  Definition pid : Set := string.

  Variant action : Type :=
  | Send (c : chan) : action
  | Rcv (c : chan) : action.

  (* We consider CCS with guarded choice for now *)
  Inductive term : Type :=
  | DoneT : term
  | ActionT (a : action) (P : term)
  | ParaT (P1 P2 : term)
  | RestrictT (c : chan) (P : term).
  
End Syntax.

Module CCS.

  Section Semantics.

    Definition op (a : action) : action :=
      match a with
      | Send c => Rcv c
      | Rcv c => Send c
      end.

    Definition action_eq_dec : forall (a b : action), {a = b} + {~ a = b}.
      repeat decide equality.
    Defined.

    Definition are_opposite (a b : action) : bool :=
      if action_eq_dec a (op a) then true else false.

    Variant ActionE : Type -> Type :=
    | Act (a : action) : ActionE unit.

    Variant SynchE : Type -> Type := | Synch : SynchE unit.

    Variant choice := | Left | Right | Synchronize.

    Variant SchedE : Type -> Type :=
    | Sched : SchedE choice.
    
    Definition DeadE := exceptE unit.
    Definition dead {A : Type} {E} `{DeadE -< E} : itree E A :=
      x <- trigger (Throw tt);; match x: void with end.

    Notation ccsE   := (SchedE +' ActionE +' SynchE +' DeadE).
    Notation ccsT T := (itree ccsE T).
    Notation ccs    := (ccsT unit).

    Definition done : ccs := Ret tt.

    Definition act (a : action) : ccs := trigger (Act a).

    Definition branch (P Q R : ccs) : ccs :=
      b <- trigger Sched;;
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
          | deadP e => dead
          end
        end.
    
    Definition para : ccs -> ccs -> ccs :=
      cofix F (P : ccs) (Q : ccs) := 
        branch
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
      | RestrictT c t => restrict c (model t)
      end.

  End Semantics.

End CCS.

Module CCS2.

  Section Semantics.

    Definition op (a : action) : action :=
      match a with
      | Send c => Rcv c
      | Rcv c => Send c
      end.

    Definition action_eq_dec : forall (a b : action), {a = b} + {~ a = b}.
      repeat decide equality.
    Defined.

    Definition are_opposite (a b : action) : bool :=
      if action_eq_dec a (op a) then true else false.

    Variant ActionE : Type -> Type :=
    | Act (a : action) : ActionE unit.

    Variant SynchE : Type -> Type := | Synch : SynchE unit.

    Variant choice := | Left | Right | Synchronize.

    Variant SchedE : Type -> Type :=
    | Sched2 : SchedE bool 
    | Sched3 : SchedE choice.
    
    Notation ccsE   := (SchedE +' ActionE +' SynchE).
    Notation ccsT T := (itree ccsE T).
    Notation ccs    := (ccsT unit).

    Definition done : ccs := Ret tt.

    Definition context := list chan. 
    Definition in_context (Γ : context) (c : chan) :=
      if in_dec string_dec c Γ then true else false.
    Notation "a ∈ Γ" := (in_context Γ a) (at level 10).

    Definition act Γ (a : action) : option ccs :=
      match a with
      | Send c | Rcv c => if c ∈ Γ then None else Some (trigger (Act a))
      end.
    
    Definition branch2 (P Q : ccs) : ccs :=
      b <- trigger Sched2;;
      if b : bool then P else Q.

    Definition branch3 (P Q R : ccs) : ccs :=
      b <- trigger Sched3;;
      match b with
      | Left => P
      | Right => Q
      | Synchronize => R
      end.

    Variant head := | HDone | HSynch (P : ccs) | HAct (a : action) (P : ccs).

    (* Notations for patterns *)
    Notation "'schedP' e" := (inl1 e) (at level 10).
    Notation "'actP' e" := (inr1 (inl1 e)) (at level 10).
    Notation "'synchP' e" := (inr1 (inr1 e)) (at level 10).
    
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
          end
        end.
    
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
            branch3 (vis (Act a) (fun _ => F P' Q))
                    (vis (Act b) (fun _ => F P Q'))
                    (vis Synch   (fun _ => F P' Q'))
          else
            branch2 (vis (Act a) (fun _ => F P' Q))
                    (vis (Act b) (fun _ => F P Q'))
        | HAct a P', HSynch Q' =>
          branch2 (vis (Act a) (fun _ => F P' Q))
                  (vis Synch   (fun _ => F P Q'))
        | HSynch P', HAct a Q' =>
          branch2 (vis Synch   (fun _ => F P' Q))
                  (vis (Act a) (fun _ => F P Q'))
        | HSynch P', HSynch Q' =>
          branch2 (vis Synch   (fun _ => F P' Q))
                  (vis Synch   (fun _ => F P Q'))
        end.

    Import MonadNotation.
    Open Scope monad.
    (* This approach to name restriction is incorrect *)
    Fixpoint model (Γ : context) (t : term) : option ccs :=
      match t with
      | DoneT         => ret done
      | ActionT a t   =>
        P <- act Γ a;;
        Q <- model Γ t;;
        ret (ITree.bind P (fun _ => Q))
      | ParaT t1 t2   =>
        P <- model Γ t1;;
        Q <- model Γ t2;;
        ret (para P Q)
      | RestrictT c t => model (c :: Γ) t
      end.

    (* P ==  ν a. (a || a|)

       model P [] ~ Some {Synch}

       model (a || a|) [(a,0)]

       model a [(a,n)] ~ Some {a}

para [(a,0)] {a} {a|}

       model (a || a|) [(a,0)]

     *)
    (* Inductive well_scoped: context -> term -> Prop := *)
    (* | WSdone : forall Γ, well_scoped Γ DoneT *)
    (* | WSSend : forall Γ c P, c ∈ Γ = true -> *)
    (*                     well_scoped Γ P -> *)
    (*                     well_scoped Γ (ActionT (Send c) P) *)
    (* | WSRcv : forall Γ c P, c ∈ Γ = true -> *)
    (*                    well_scoped Γ P -> *)
    (*                    well_scoped Γ (ActionT (Rcv c) P) *)
    (* | WSpara : forall Γ P Q, *)
    (*     well_scoped Γ P -> *)
    (*     well_scoped Γ Q -> *)
    (*     well_scoped Γ (ParaT P Q) *)
    (* | WSrestrict : forall Γ c P, *)
    (*     well_scoped (c::Γ) P -> *)
    (*     well_scoped Γ (RestrictT c P) *)
    (* . *)

    (* Lemma WS_succeed : *)
    (*   forall Γ P, *)
    (*     well_scoped Γ P -> *)
    (*     exists ccs, model Γ P = Some ccs.  *)
    (* Proof. *)
    (*   induction 1. *)
    (*   - eexists; reflexivity. *)
    (*   - cbn. *)
    (*     rewrite H. *)
    (*     destruct IHwell_scoped as (? & EQ); rewrite EQ. *)
    (*     eexists; reflexivity. *)
    (*   - cbn. *)
    (*     rewrite H. *)
    (*     destruct IHwell_scoped as (? & EQ); rewrite EQ. *)
    (*     eexists; reflexivity. *)
    (*   - cbn. *)
    (*     destruct IHwell_scoped1 as (? & EQ); rewrite EQ. *)
    (*     destruct IHwell_scoped2 as (? & EQ'); rewrite EQ'. *)
    (*     eexists; reflexivity. *)
    (*   - cbn. *)
    (*     destruct IHwell_scoped as (? & EQ); rewrite EQ. *)
    (*     eexists; reflexivity. *)
    (* Qed. *)

    (* Lemma closed_processes_are_denoted : *)
    (*   forall P, *)
    (*     well_scoped nil P -> *)
    (*     exists ccs, model nil P = Some ccs.  *)
    (* Proof. *)
    (*   intros; eapply WS_succeed; eauto. *)
    (* Qed. *)

  End Semantics.

End CCS2.
