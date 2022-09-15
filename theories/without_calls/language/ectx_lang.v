From tmc.without_calls.language Require Import
  lang.

Section ectx_language_mixin.
  Context {expr val ectx state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (head_step : expr → state → expr → state → Prop).

  Record EctxLanguageMixin := {
    mixin_to_of_val v :
      to_val (of_val v) = Some v ;
    mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    mixin_val_head_stuck e1 σ1 e2 σ2 :
      head_step e1 σ1 e2 σ2 →
      to_val e1 = None ;
    mixin_fill_empty e :
      fill empty_ectx e = e ;
    mixin_fill_comp K1 K2 e :
      fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e ;
    mixin_fill_inj K :
      Inj (=) (=) (fill K) ;
    mixin_fill_val K e :
      is_Some (to_val (fill K e)) →
      is_Some (to_val e) ;
    mixin_step_by_val K' K_redex e1' e1_redex σ1 e2 σ2 :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step e1_redex σ1 e2 σ2 →
      ∃ K'', K_redex = comp_ectx K' K'' ;
    mixin_head_ctx_step_val K e σ1 e2 σ2 :
      head_step (fill K e) σ1 e2 σ2 →
      is_Some (to_val e) ∨ K = empty_ectx ;
  }.
End ectx_language_mixin.

Structure ectxLanguage := EctxLanguage {
  expr : Type ;
  val : Type ;
  ectx : Type ;
  state : Type ;
  of_val : val → expr ;
  to_val : expr → option val ;
  empty_ectx : ectx ;
  comp_ectx : ectx → ectx → ectx ;
  fill : ectx → expr → expr ;
  head_step : expr → state → expr → state → Prop ;
  ectx_language_mixin :
    EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill head_step ;
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments EctxLanguage {_ _ _ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments empty_ectx {_}.
Global Arguments comp_ectx {_} _ _.
Global Arguments fill {_} _ _.
Global Arguments head_step {_} _ _ _ _.

Section ectx_language.
  Context {Λ : ectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.
  Implicit Types σ : state Λ.

  Lemma val_head_stuck e1 σ1 e2 σ2 :
    head_step e1 σ1 e2 σ2 → to_val e1 = None.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply ectx_language_mixin. Qed.
  Lemma step_by_val K' K_redex e1' e1_redex σ1 e2 σ2 :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step e1_redex σ1 e2 σ2 →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_ctx_step_val K e σ1 e2 σ2 :
    head_step (fill K e) σ1 e2 σ2 → is_Some (to_val e) ∨ K = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.

  Definition head_reducible e σ :=
    ∃ e' σ', head_step e σ e' σ'.
  Definition head_irreducible e σ :=
    ∀ e' σ', ¬ head_step e σ e' σ'.
  Definition head_stuck e σ :=
    to_val e = None ∧ head_irreducible e σ.

  Definition sub_redexes_are_values e :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step e1 σ1 e2 σ2 : Prop :=
    | Ectx_step K e1' e2' :
        e1 = fill K e1' →
        e2 = fill K e2' →
        head_step e1' σ1 e2' σ2 →
        prim_step e1 σ1 e2 σ2.

  Lemma Ectx_step' K e1 σ1 e2 σ2 :
    head_step e1 σ1 e2 σ2 → prim_step (fill K e1) σ1 (fill K e2) σ2.
  Proof. econstructor; eauto. Qed.

  Definition ectx_lang_mixin : LanguageMixin of_val to_val prim_step.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros ? ? ? ? [? ? ? -> -> ?%val_head_stuck].
      apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
  Qed.

  Canonical Structure ectx_lang : language := Language ectx_lang_mixin.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma not_head_reducible e σ : ¬ head_reducible e σ ↔ head_irreducible e σ.
  Proof. unfold head_reducible, head_irreducible. naive_solver. Qed.

  Lemma head_redex_unique K K' e e' σ :
    fill K e = fill K' e' →
    head_reducible e σ →
    head_reducible e' σ →
    K = comp_ectx K' empty_ectx ∧ e = e'.
  Proof.
    intros Heq (e2 & σ2 & Hred) (e2' & σ2' & Hred').
    edestruct (step_by_val K' K e' e) as [K'' HK];
      [by eauto using val_head_stuck..|].
    subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
    destruct (head_ctx_step_val _ _ _ _ _ Hred') as [[]%not_eq_None_Some|HK''].
    { by eapply val_head_stuck. }
    subst K''. rewrite fill_empty. done.
  Qed.

  Lemma head_prim_step e1 σ1 e2 σ2 :
    head_step e1 σ1 e2 σ2 →
    prim_step e1 σ1 e2 σ2.
  Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma head_step_not_stuck e σ e' σ' :
    head_step e σ e' σ' → not_stuck e σ.
  Proof. rewrite /not_stuck /reducible /=. eauto 10 using head_prim_step. Qed.

  Lemma fill_prim_step K e1 σ1 e2 σ2 :
    prim_step e1 σ1 e2 σ2 → prim_step (fill K e1) σ1 (fill K e2) σ2.
  Proof.
    destruct 1 as [K' e1' e2' -> ->].
    rewrite !fill_comp. by econstructor.
  Qed.
  Lemma fill_reducible K e σ :
    reducible e σ → reducible (fill K e) σ.
  Proof.
    intros (e'&σ'&?). exists (fill K e'), σ'.
    by apply fill_prim_step.
  Qed.
  Lemma head_prim_reducible e σ :
    head_reducible e σ → reducible e σ.
  Proof. intros (e'&σ'&?). eexists e', σ'. by apply head_prim_step. Qed.
  Lemma head_prim_fill_reducible e K σ :
    head_reducible e σ → reducible (fill K e) σ.
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  Lemma head_prim_irreducible e σ :
    irreducible e σ → head_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_reducible e σ :
    reducible e σ → sub_redexes_are_values e → head_reducible e σ.
  Proof.
    intros (e'&σ'&[K e1' e2' -> -> Hstep]) ?.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty /head_reducible; eauto.
  Qed.
  Lemma prim_head_irreducible e σ :
    head_irreducible e σ → sub_redexes_are_values e → irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck e σ :
    head_stuck e σ → sub_redexes_are_values e → stuck e σ.
  Proof.
    intros [] ?. split; first done.
    by apply prim_head_irreducible.
  Qed.

  Lemma head_reducible_prim_step_ctx K e1 σ1 e2 σ2 :
    head_reducible e1 σ1 →
    prim_step (fill K e1) σ1 e2 σ2 →
    ∃ e2', e2 = fill K e2' ∧ head_step e1 σ1 e2' σ2.
  Proof.
    intros (e2''&σ2''&HhstepK) [K' e1' e2' HKe1 -> Hstep].
    edestruct (step_by_val K) as [K'' ?];
      eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply head_ctx_step_val in HhstepK as [[v ?]|?]; simplify_eq.
    { apply val_head_stuck in Hstep; simplify_eq. }
    by rewrite !fill_empty.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 e2 σ2 :
    head_reducible e1 σ1 →
    prim_step e1 σ1 e2 σ2 →
    head_step e1 σ1 e2 σ2.
  Proof.
    intros.
    edestruct (head_reducible_prim_step_ctx empty_ectx) as (?&?&?);
      rewrite ?fill_empty; eauto.
    by simplify_eq; rewrite fill_empty.
  Qed.

  Global Instance ectx_lang_ctx K : LanguageCtx (fill K).
  Proof.
    split; simpl.
    - eauto using fill_not_val.
    - intros ? ? ? ? [K' e1' e2' Heq1 Heq2 Hstep].
      by exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp.
    - intros e1 σ1 e2 σ2 Hnval [K'' e1'' e2'' Heq1 -> Hstep].
      destruct (step_by_val K K'' e1 e1'' σ1 e2'' σ2) as [K' ->]; eauto.
      rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
      exists (fill K' e2''); rewrite -fill_comp; split; auto.
      econstructor; eauto.
  Qed.

  Record pure_head_step e1 e2 := {
    pure_head_step_safe σ1 :
      head_reducible e1 σ1;
    pure_head_step_det σ1 e2' σ2 :
      head_step e1 σ1 e2' σ2 →
      σ2 = σ1 ∧ e2' = e2
  }.

  Lemma pure_head_step_pure_step e1 e2 :
    pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros σ. destruct (Hp1 σ) as (e2' & σ2 & ?).
      eexists e2', σ2. by apply head_prim_step.
    - intros σ1 e2' σ2 ?%head_reducible_prim_step; auto.
  Qed.

  Lemma pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill K e1) (fill K e2).
  Proof. apply: pure_exec_ctx. Qed.
End ectx_language.

Global Arguments ectx_lang : clear implicits.
Global Arguments Ectx_step {Λ e1 σ1 e2 σ2}.
Coercion ectx_lang : ectxLanguage >-> language.

Definition LanguageOfEctx (Λ : ectxLanguage) : language :=
  let '@EctxLanguage E V C St of_val to_val empty comp fill head mix := Λ in
  @Language E V St of_val to_val _
    (@ectx_lang_mixin (@EctxLanguage E V C St of_val to_val empty comp fill head mix)).
Global Arguments LanguageOfEctx : simpl never.
