From Coq Require ExtrOcamlBasic ExtrOcamlString.

From CCS Require Import Syntax Denotational.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z.

Set Extraction AccessOpaque.

(* Definition p := (model (ex DoneT DoneT)). *)
Definition p := (model (ActionT (Send "a") DoneT)).

Extraction "model.ml" p.
