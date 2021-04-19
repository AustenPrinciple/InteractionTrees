From Coq Require ExtrOcamlBasic ExtrOcamlString.

From CCS Require Import Denotational.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z.

Set Extraction AccessOpaque.

Extraction "CCS.ml" model.
