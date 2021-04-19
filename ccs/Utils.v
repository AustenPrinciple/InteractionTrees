(* begin hide *)
From ITree Require Import
     ITree
.

Inductive Fitree {E : Type -> Type} {X : Type} : Type :=
| FBot : Fitree
| FRet : X -> Fitree
| FTau : Fitree -> Fitree 
| FVis {Y} : E Y -> (Y -> Fitree) -> Fitree
.
Arguments Fitree : clear implicits.

Fixpoint prefix {E X} (n: nat) (t : itree E X) : Fitree E X :=
  match n with
  | O => FBot
  | S n =>
    match observe t with
    | RetF x => FRet x
    | TauF t => FTau (prefix n t)
    | VisF e k => FVis e (fun x => prefix n (k x))
    end
  end.

Definition eval {E X} := @prefix E X 100.
