(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
(* end hide *)

(* Simple program:
 * VM := coin.(/tea + /coffee). VM
 * Student := /coin.tea./paper
 * VM | Student
 *
 * observable effects:
 * coin (internal), tea (internal), paper (external)
 *)
Definition chan : Set := string.
Definition value : Type := nat.

Inductive expr : Type :=
| Nil : expr
| ActSend (c : chan) (v : value) (p : expr)
| ActRecv (c : chan) (v : value) (p : expr)
| Recur (x : string)
| Choice (p1 p2 : expr)
| Para (p1 p2 : expr)
| Subst (p : expr) (b a : chan)
| Restrict (p : expr) (c : chan).

Inductive CommE : Type -> Type :=
| Send : chan -> value -> CommE unit
| Receive : chan -> CommE value.

Inductive SchedE : Type -> Type :=
| SChoice : expr -> expr -> SchedE bool
| SPara : SchedE bool.

Definition plus_one_a : itree CommE unit :=
  x <- ITree.trigger (Receive "a") ;;
  ITree.trigger (Send "a" (x + 1)).

Definition handle_comm :
  forall R, CommE R ->
       Monads.stateT nat (itree void1) R :=
  fun R e last_rec =>
    match e with
    (* we ignore channels for now *)
    | Send _ x => ret (x, tt)
    | Receive _ => ret (last_rec, last_rec)
    end.

Definition interp_comm :
  forall R, itree CommE R -> itree void1 (nat * R) :=
  fun R t => interp handle_comm t 0.

Definition interpreted_plus_one : itree void1 (nat * unit) :=
  interp_comm _ plus_one_a.

Compute (burn 100 interpreted_plus_one).

Definition denote_expr : expr -> (string * string) map ->
                         itree (CallE +' CommE +' SchedE) unit  :=
  rec
    (fun e m =>
       match e with
       | Nil => ret tt
       | ActSend c v p => match get m c with
                         (* This channel has been restricted *)
                         | Some "" => Tau p m
                         (* Some substitution has happened *)
                         | Some x => trigger (Send x v) ;;
                                    Call p m
                         (* No information, fresh channel so we proceed as normal *)
                         | None => trigger (Send c v) ;;
                                  Call p m
                         end
       | ActRecv c p => match get m c with
                       (* This channel has been restricted *)
                       | Some "" => Tau p m
                       (* Some substitution has happened *)
                       | Some x => trigger (Receive x) ;;
                                  Call p m
                       (* No information, fresh channel so we proceed as normal *)
                       | None => trigger (Receive c) ;;
                                Call p m
                       end
       (* This one is a special version of a recursive call *)
       | Recur p => Call p m
       | Choice p1 Nil => Call p1 m
       | Choice Nil p2 => Call p2 m
       (* The previous two could be collapsed into the next,
        * depending on how the choice is implemented *)
       | Choice p1 p2 => b <- trigger (SChoice p1 p2) ;;
                        if b then Call p1 m
                        else Call p2 m
       | Para p1 p2 => b <- trigger SPara ;;
                      if b then
                        let x, p1' = Call p1 m in
                        (* if some subst/restrict happened in x, we need a way
                         * to transfer that information to p1' but not to p2 *)
                        x, Para (p1', p2)
                      else
                        let x, p2' = Call p2 m in
                        (* same with p2' *)
                        x, Para (p1, p2')
       | Subst p b a => Call p (set m a b)
       | Restrict p c => Call p (set m "" c)
       end.
