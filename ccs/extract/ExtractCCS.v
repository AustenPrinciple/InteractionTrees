From Coq Require ExtrOcamlBasic ExtrOcamlString.
From ITree Require Import
     ITree
     Eq.Eq
     Events.Exception
     ITreeFacts.


From CCS Require Import Syntax Denotational.

Import CCSNotations.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z.

Set Extraction AccessOpaque.

(* Definition p := (model (ex DoneT DoneT)). *)
Definition p1 := model 0.

Definition p2 := model (↑ "a" ⋅ 0 ).

Definition p3 := model (↑ "a" ⋅ 0 ∥ ↓ "a" ⋅ 0).

(* {?a !a; !a ?a; τ} *)
Definition p4 := model (↓ "a" ⋅ 0 ∥ ↑ "a" ⋅ 0).

(* {?a !b; !b ?a} *)
Definition p5 := model (↓ "a" ⋅ 0 ∥ ↑ "b" ⋅ 0).

(* {τ} *)
Definition p6 := model ((↓ "a" ⋅ 0 ∥ ↑ "a" ⋅ 0) ∖ "a").

(* {} *)
Definition p7 := model ((↓ "a" ⋅ 0 ∥ ↑ "b" ⋅ 0) ∖ "a").

Definition p8 := model (((↓ "a" ⋅ 0 ∥ ↑ "b" ⋅ 0) ∖ "a") ∥ (↓ "b" ⋅ 0)).

Extraction "model.ml" p1 p2 p3 p4 p5 p6 p7 p8.
