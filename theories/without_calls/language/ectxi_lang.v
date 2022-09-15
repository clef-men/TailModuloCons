From tmc.without_calls.language Require Import
  lang
  ectx_lang.

Section ectxi_language_mixin.

  Context {expr val ectx_item state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (fill_item : ectx_item → expr → expr).
  Context (head_step : expr → state → expr → state → Prop).

  Record EctxiLanguageMixin := {
    mixin_to_of_val v :
      to_val (of_val v) = Some v ;
    mixin_of_to_val e v :
      to_val e = Some v → of_val v = e ;
    mixin_val_stuck e1 σ1 e2 σ2 :
      head_step e1 σ1 e2 σ2 → to_val e1 = None ;
    mixin_fill_item_val Ki e :
      is_Some (to_val (fill_item Ki e)) → is_Some (to_val e) ;
    mixin_fill_item_inj Ki :
      Inj (=) (=) (fill_item Ki) ;
    mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
      to_val e1 = None → to_val e2 = None →
      fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2 ;
    mixin_head_ctx_step_val Ki e σ1 e2 σ2 :
      head_step (fill_item Ki e) σ1 e2 σ2 → is_Some (to_val e) ;
  }.

End ectxi_language_mixin.

Structure ectxiLanguage := EctxiLanguage {
  expr : Type;
  val : Type;
  ectx_item : Type;
  state : Type;
  of_val : val → expr;
  to_val : expr → option val;
  fill_item : ectx_item → expr → expr;
  head_step : expr → state → expr → state → Prop;
  ectxi_language_mixin : EctxiLanguageMixin of_val to_val fill_item head_step
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Global Arguments EctxiLanguage {_ _ _ _ _ _ _ _} _.
Global Arguments of_val {_} _.
Global Arguments to_val {_} _.
Global Arguments fill_item {_} _ _.
Global Arguments head_step {_} _ _ _ _.

Section ectxi_language.

  Context {Λ : ectxiLanguage}.
  Implicit Types (e : expr Λ).
  Implicit Types (Ki : ectx_item Λ).
  Notation ectx := (list (ectx_item Λ)).
  Implicit Types (K : ectx).

  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma head_ctx_step_val Ki e σ1 e2 σ2 :
    head_step (fill_item Ki e) σ1 e2 σ2 → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.

  Definition fill K e := foldl (flip fill_item) e K.

  Lemma fill_app K1 K2 e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
  Proof. apply foldl_app. Qed.

  Definition ectxi_lang_ectx_mixin :
    EctxLanguageMixin of_val to_val [] (flip (++)) fill head_step.
  Proof.
    assert (fill_val : ∀ K e, is_Some (to_val (fill K e)) → is_Some (to_val e)).
    { intros K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. }
    assert (fill_not_val : ∀ K e, to_val e = None → to_val (fill K e) = None).
    { intros K e. rewrite !eq_None_not_Some. eauto. }
    split.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - done.
    - intros K1 K2 e. by rewrite /fill /= foldl_app.
    - intros K; induction K as [|Ki K IH]; rewrite /Inj; naive_solver.
    - done.
    - intros K K' e1 e1' σ1 e2 σ2 Hfill Hred Hstep; revert K' Hfill.
      induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
      destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
      { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
        apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
      rewrite !fill_app /= in Hfill.
      assert (Ki = Ki') as ->.
      { eapply fill_item_no_val_inj, Hfill; eauto using val_head_stuck.
        apply fill_not_val. revert Hstep. apply ectxi_language_mixin. }
      simplify_eq. destruct (IH K') as [K'' ->]; auto.
      exists K''. by rewrite assoc.
    - intros K e1 σ1 e2 σ2.
      destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
      rewrite fill_app /=.
      intros ?%head_ctx_step_val; eauto using fill_val.
  Qed.

  Canonical Structure ectxi_lang_ectx := EctxLanguage ectxi_lang_ectx_mixin.
  Canonical Structure ectxi_lang := LanguageOfEctx ectxi_lang_ectx.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_item Ki e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val, Hsub. by rewrite /= fill_app.
  Qed.

  Global Instance ectxi_lang_ctx_item Ki : LanguageCtx (fill_item Ki).
  Proof. change (LanguageCtx (fill [Ki])). apply _. Qed.

End ectxi_language.

Global Arguments ectxi_lang_ectx : clear implicits.
Global Arguments ectxi_lang : clear implicits.
Coercion ectxi_lang_ectx : ectxiLanguage >-> ectxLanguage.
Coercion ectxi_lang : ectxiLanguage >-> language.

Definition EctxLanguageOfEctxi (Λ : ectxiLanguage) : ectxLanguage :=
  let '@EctxiLanguage E V C St of_val to_val fill head mix := Λ in
  @EctxLanguage E V (list C) St of_val to_val _ _ _ _
    (@ectxi_lang_ectx_mixin (@EctxiLanguage E V C St of_val to_val fill head mix)).

Global Arguments EctxLanguageOfEctxi : simpl never.
