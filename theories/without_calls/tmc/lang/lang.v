From simuliris.common Require Import
  prelude
  tactics.
From simuliris.without_calls Require Export
  lang.ectxi_lang.
From simuliris.without_calls.tmc Require Export
  lang.semantics.

Notation of_val := Val.

Definition to_val e :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Global Instance ectxi_lang_ctxi_base : LangCtxiBase expr ectxi :=
  ectxi_fill.
Lemma tmc_lang_mixin :
  EctxiLangMixin of_val to_val head_step ectxi.
Proof.
  econstructor; last (econstructor; first econstructor).
  - naive_solver.
  - intros []; naive_solver.
  - intros * []; naive_solver.
  - intros [] ?**; naive_solver.
  - intros []; naive_solver.
  - intros [] []; naive_solver.
  - intros [] * Hstep; invert Hstep; naive_solver.
Qed.

Canonical tmc_ectxi_lang := Build_ectxi_lang tmc_lang_mixin.
Canonical tmc_ectx_lang := ectx_lang_of_ectxi_lang tmc_ectxi_lang.
Canonical tmc_lang := lang_of_ectx_lang tmc_ectx_lang.

Global Instance ctxi_lang_ctxi_base : LangCtxiBase expr ctxi :=
  ctxi_fill.
Program Global Instance ctxi_lang_ctxi : LangCtxi tmc_lang ctxi :=
  Build_LangCtxi _.
Next Obligation.
  simpl. econstructor.
  - intros [] ?**; naive_solver.
  - intros []; naive_solver.
Qed.
Global Instance ctx_lang_ctx : LangCtx tmc_lang ctx :=
  _.
