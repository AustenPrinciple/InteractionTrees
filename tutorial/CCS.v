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
     Events.StateFacts
     Interp.Recursion
     Events.Exception.

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

Section Syntax.

  Definition chan : Set := string.
  Definition value : Type := nat.
  Definition pid : Set := string.

  Variant action : Type :=
  | Send (c : chan) (v : value) : action
  | Rcv (c : chan) : action.

  Inductive term : Type :=
  | Nil : term
  | Action (a : action) (p : term)
  | CallP (x : pid)
  | Choice (p1 p2 : term)
  | Para (p1 p2 : term)
  | Subst (p : term) (b a : chan)
  | Restrict (p : term) (c : chan).

End Syntax.

Section Representation.

  (* We want to represent syntactic terms of CCS as uninterpreted
     interaction trees representing their possible dynamic behaviors.

     For now, we consider _asynchronous_ communications.
   *)

  (* [CommE] are the communication action *)
  Variant CommE : Type -> Type :=
  | SendE : chan -> value -> CommE unit
  | ReceiveE : chan -> CommE value.

  (* [SchedE] represents the internal and external non-determinism *)
  Variant SchedE : Type -> Type :=
  | SChoice : term -> term -> SchedE bool
  | SPara : SchedE bool.

  Variant CallProcessE : Type -> Type :=
  | CallProcess (p : pid) : CallProcessE unit.

  Definition FailureE := exceptE string.  

  Definition E := CallProcessE +' CommE +' SchedE +' FailureE.

  Definition throw {A : Type} {E} `{exceptE string -< E}
             (s: string) : itree E A :=
    x <- trigger (Throw s);; match x: void with end.

  (*
The internal divergence has a tricky behavior: it can only takes
a branch that exhibits a reduction.

One solution would seem to be to introspect the branch and fail if we
do not find an action to perform.

However, this process is not purely syntactic due to the mutually recursive processes: it could diverge in the case of:

    f := rec g
    g := rec f

What is the right solution to this problem?

Conjecture: it suffices to explore the recursive calls until we reach a cycle.

   *)

  Fixpoint get_next_action (t : term) :
    itree (callE term unit +' E) (term * action) :=
    match t with
    | Nil => throw "No action found in this internal branch"
    | Action a t => ret (t, a)
    | CallP _ => throw "TODO: This is a restriction" 
    | Choice t1 t2 =>
      b <- trigger (SChoice t1 t2);;
      if b:bool
      then get_next_action t1
      else get_next_action t2
    | Para t1 t2 =>
      b <- trigger SPara;;
      if b:bool
      then
        '(t1',a) <- get_next_action t1;;
        ret (Para t1' t2, a)
      else 
        '(t2',a) <- get_next_action t1;;
        ret (Para t1 t2', a)
    | Subst _ _ _ => throw "TODO"
    | Restrict _ _ => throw "TODO"
    end. 

  Definition do_action (a : action) :
    itree (callE term unit +' E) unit :=
    match a with
    | Send c v => trigger (SendE c v)
    | Rcv c    => trigger (ReceiveE c);; ret tt (* We currently dismiss the value sent over the canal *)
    end.
  
  Definition denote_term : term ->
                           (* (string * string) map -> *)
                           itree E unit.
    refine
      (rec (fun t => _)).
    refine (
        match t with
        | Nil => ret tt
        | Action a p =>
          match a with
          | Send c v =>
            (* This ignores scopes for now *)
            trigger (SendE c v);;
            trigger (Call p)
          | Rcv c =>
            (* This ignores scopes for now *)
            trigger (ReceiveE c);;
            trigger (Call p)
          end

        (* This one is a special version of a recursive call *)
        | CallP p => trigger (CallProcess p)

        | Choice p1 p2 =>
          b <- trigger (SChoice p1 p2) ;;
          if b: bool
          then
            '(t',a) <- get_next_action p1;;
            do_action a;;
            trigger (Call t')
          else 
            '(t',a) <- get_next_action p2;;
            do_action a;;
            trigger (Call t')
        | Para t1 t2 => throw "TODO"
        | Subst _ _ _ => throw "TODO"
        | Restrict _ _ => throw "TODO"
        end).

(*
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

*)
