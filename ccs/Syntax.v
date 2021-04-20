(* begin hide *)

From Coq Require Export
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
  | PlusT (P1 P2 : term)
  | RestrictT (c : chan) (P : term).
  
End Syntax.

Definition op (a : action) : action :=
  match a with
  | Send c => Rcv c
  | Rcv c => Send c
  end.

Definition action_eq_dec : forall (a b : action), {a = b} + {~ a = b}.
  repeat decide equality.
Defined.

Definition are_opposite (a b : action) : bool :=
  if action_eq_dec a (op b) then true else false.

Module CCSNotations.

  Declare Scope ccs_scope.

  Notation "0" := DoneT : ccs_scope.
  Notation "a ⋅ P" := (ActionT a P) (at level 10) : ccs_scope.
  Notation "P ∥ Q" := (ParaT P Q) (at level 29, left associativity) : ccs_scope.
  Notation "P ⊕ Q" := (PlusT P Q) (at level 20, left associativity) : ccs_scope.
  Notation "P ∖ c" := (RestrictT c P) (at level 10) : ccs_scope.
  Notation "↑" := Send.
  Notation "↓" := Rcv.

End CCSNotations.

Import CCSNotations.
Open Scope ccs_scope.

Section Ex.

  Definition a := "a".
  Definition b := "b".

  Definition ex P Q : term :=
    ((↑a ⋅ P ⊕ ↑b ⋅ 0) ∥ ↓a ⋅ Q) ∖ a.

End Ex.
