(** * Dependently-typed effects *)

(** A _type family_ is given by a parameter type [I : Type] and a type function
    [F : I -> Type].

    A type family [(I, F : I -> Type)] can be encoded as an indexed type
    [E : Type -> Type].
    A value [i : I] can be seen as a "flat representation" of a value [e : E X]
    (for arbitrary [X]), while [F i : Type] gives the type index [X] of this [e].

    This encoding can be seen as a kind of "dependently-typed effect".
 *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Core.ITree
     Indexed.Sum
     Indexed.OpenSum.

Import Basics.Basics.Monads.
(* end hide *)

Variant depE {I : Type} (F : I -> Type) : Type -> Type :=
| Dep (i : I) : depE F (F i).

Arguments Dep {I F}.

Definition dep {I F E} `{depE F -< E} (i : I) : itree E (F i) :=
  send (Dep i).

Definition undep {I F} (f : forall i : I, F i) :
  depE F ~> identity :=
  fun _ d =>
    match d with
    | Dep i => f i
    end.
