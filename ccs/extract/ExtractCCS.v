From Coq Require ExtrOcamlBasic ExtrOcamlString.
From ITree Require Import
     ITree
     Eq.Eq
     Events.Exception
     ITreeFacts.


From CCS Require Import Syntax Denotational.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z.

Set Extraction AccessOpaque.

(* Definition p := (model (ex DoneT DoneT)). *)
Definition p1 := (model  DoneT).

Definition p2 := (model (ActionT (Send "a") DoneT)).

Definition p3 := (model (ParaT (ActionT (Send "a") DoneT) (ActionT (Rcv "a") DoneT))).

Definition p4 := (model (ParaT (ActionT (Rcv "a") DoneT) (ActionT (Send "a") DoneT))).

Definition p5 := (model (ParaT (ActionT (Send "a") DoneT) (ActionT (Rcv "b") DoneT))).

Extraction "model.ml" p1 p2 p3 p4 p5.
