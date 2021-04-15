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
     Strings.String.

(* end hide *)

Open Scope string.

Module CCS.

  Section Syntax.

    Definition chan : Set := string.
    Definition pid : Set := string.

    Variant action : Type :=
    | Send (c : chan) : action
    | Rcv (c : chan) : action.

    (* We consider CCS with guarded choice for now *)
    Inductive term : Type :=
    | NilT : term
    | ActionT (a : action) (P : term)
    | ParaT (P1 P2 : term)
    | RestrictT (c : chan) (P : term).

  End Syntax.

  (* Comment faire un opérateur parallèle qui combine les trois "types" de comportements de (P1 || P2):
   P1 expose au moinde extérieur une action
   P2 expose au moinde extérieur une action
   P1 et P2 font une synchro

   ⟦ P ⟧ : term -> itree E unit/term

   *)

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
      match action_eq_dec a (op a) with
      | left _ => true
      | right _ => false
      end.

    Variant ActionE : Type -> Type :=
    | Act (a : action) : ActionE unit.

    Variant SynchE : Type -> Type := | Synch : SynchE unit.

    Variant choice := | Left | Right | Synchronize.

    Variant SchedE : Type -> Type :=
    | Sched : SchedE choice.
    
    Definition DeadE := exceptE unit.
    Definition dead {A : Type} {E} `{DeadE -< E} : itree E A :=
      x <- trigger (Throw tt);; match x: void with end.

    Notation ccsE := (SchedE +' ActionE +' SynchE +' DeadE).
    Notation ccsT T := (itree ccsE T).
    Notation ccs := (ccsT unit).

    Definition nil : ccs := Ret tt.
    Definition act (a : action) : ccs := trigger (Act a).

    Definition branch (P Q R : ccs) : ccs :=
      b <- trigger Sched;;
      match b with
      | Left => P
      | Right => Q
      | Synchronize => R
      end.

    Variant head := | HDone | HSynch (P : ccs) | HAct (a : action) (P : ccs).

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
      | NilT          => nil
      | ActionT a t   => act a;; model t
      | ParaT t1 t2   => para (model t1) (model t2)
      | RestrictT c t => restrict c (model t)
      end.

  End Semantics.

End CCS.

