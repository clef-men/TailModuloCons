From tmc.common Require Import
  prelude.
From tmc.without_calls.language Require Export
  lang
  ectx_lang
  ectxi_lang.
From tmc.without_calls.tmc_lang Require Export
  syntax
  semantics.

Module lang.
  Notation of_val := Val (only parsing).

  Definition to_val e :=
    match e with
    | Val v => Some v
    | _ => None
    end.

  Lemma to_of_val v :
    to_val (of_val v) = Some v.
  Proof.
    by destruct v.
  Qed.

  Lemma of_to_val e v :
    to_val e = Some v → of_val v = e.
  Proof.
    destruct e; simpl; intros [= ->]; done.
  Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof.
    congruence.
  Qed.

  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof.
    induction Ki; try destruct i; intros ? ? ?; simplify_eq /=; congruence.
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof.
    intros [v ?]. induction Ki; try destruct i; simplify_option_eq; eauto.
  Qed.

  Lemma val_head_stuck e1 σ1 e2 σ2 :
    head_step e1 σ1 e2 σ2 → to_val e1 = None.
  Proof.
    destruct 1; naive_solver.
  Qed.

  Lemma head_ctx_step_val Ki e σ1 e2 σ2 :
    head_step (fill_item Ki e) σ1 e2 σ2 → is_Some (to_val e).
  Proof.
    revert e2. induction Ki; try destruct i;
    inversion_clear 1; simplify_option_eq; eauto.
  Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    revert Ki1. induction Ki2, Ki1; try destruct i; try destruct i0;
    naive_solver eauto with f_equal.
  Qed.

  Lemma alloc_fresh v1 v2 σ :
    let l := fresh_locs $ dom (gset loc) σ in
    head_step
      (PairDet (Val v1) (Val v2)) σ
      (Val $ Loc l) (<[l := (v1, v2)]> σ).
  Proof.
    apply StepPairDet; last done.
    apply (not_elem_of_dom (D := gset loc)).
    setoid_rewrite <- loc_add_0. by apply fresh_locs_fresh.
  Qed.

  Lemma mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
      fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.
End lang.

Canonical Structure ectxi_lang := EctxiLanguage lang.mixin.
Canonical Structure ectx_lang := EctxLanguageOfEctxi ectxi_lang.
Canonical Structure lang := LanguageOfEctx ectx_lang.

Export lang.

Lemma to_val_fill_some K e v :
  to_val (fill K e) = Some v →
  K = [] ∧ e = Val v.
Proof.
  intro H. destruct K as [|Ki K]; first by apply of_to_val in H. exfalso.
  assert (to_val e ≠ None) as He.
  { intro A. by rewrite fill_not_val in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (Ki :: K) (Val w)) = None).
  { destruct Ki; try destruct i; simpl; apply fill_not_val; done. }
  by simplify_eq.
Qed.

Lemma to_val_fill_none e K :
  to_val e = None →
  to_val (fill K e) = None.
Proof.
  intros H; destruct (to_val (fill K e)) eqn: Hval; auto.
  apply to_val_fill_some in Hval as [_ ->]. discriminate.
Qed.

Lemma prim_step_to_val_is_head_step e σ1 w σ2 :
  prim_step e σ1 (Val w) σ2 →
  head_step e σ1 (Val w) σ2.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.
