From Coq.Program Require Import
  Tactics.

From tmc.common Require Import
  prelude.

Ltac invert H :=
  inversion_clear H; simplify_eq.
Ltac simple_invert H :=
  simple inversion H; clear H; simplify_eq.

Ltac simplify :=
  program_simplify.
