From Coq.Program Require Import
  Tactics.

From simuliris.common Require Import
  prelude.

Ltac simplify :=
  program_simplify; simplify_eq/=.

Ltac invert H :=
  inversion H; clear H; simplify_eq/=.
