From simuliris.common Require Import
  prelude
  tactics.
From simuliris.without_calls Require Export
  lang.ectx_lang.

Section LangEctxiMixin.
  Context {val expr state : Type}.
  Context (to_val : expr → option val).
  Context (head_step : expr → state → expr → state → Prop).
  Context (ectxi : Type) `{LangCtxiBase expr ectxi}.
  Implicit Types e : expr.
  Implicit Types k : ectxi.

  Record LangEctxiMixin := {
    lang_ectxi_mixin_ctxi_mixin :
      LangCtxiMixin to_val ectxi ;
    lang_ectxi_mixin_fill_no_val_inj k1 k2 e1 e2 :
      to_val e1 = None →
      to_val e2 = None →
      k1 @@ e1 = k2 @@ e2 →
      k1 = k2 ;
    lang_ectxi_mixin_fill_head_step_val k e1 σ1 e2 σ2 :
      head_step (k @@ e1) σ1 e2 σ2 →
      is_Some (to_val e1) ;
  }.
End LangEctxiMixin.
Global Arguments Build_LangEctxiMixin {_ _ _ _ _ _ _} _ _ _ : assert.

Section lang_ectxi_mixin.
  Context {val expr state : Type}.
  Context {to_val : expr → option val}.
  Context {head_step : expr → state → expr → state → Prop}.
  Context `{LangCtxiBase expr ectxi}.
  Context (lang_ectxi_mixin : LangEctxiMixin to_val head_step ectxi).
  Implicit Types k : ectxi.

  Global Instance lang_ectxi_mixin_fill_inj k :
    Inj (=) (=) (k @@.).
  Proof.
    eauto using lang_ectxi_mixin_ctxi_mixin, lang_ctxi_mixin_fill_inj.
  Qed.
  Lemma lang_ectxi_mixin_fill_not_val k e :
    to_val e = None →
    to_val (k @@ e) = None.
  Proof.
    eauto using lang_ectxi_mixin_ctxi_mixin, lang_ctxi_mixin_fill_not_val.
  Qed.
  Lemma lang_ectxi_mixin_fill_val k e :
    is_Some (to_val (k @@ e)) →
    is_Some (to_val e).
  Proof.
    eauto using lang_ectxi_mixin_ctxi_mixin, lang_ctxi_mixin_fill_val.
  Qed.

  Let ectx := list ectxi.
  Implicit Types K : ectx.

  Lemma lang_ectxi_mixin_ectx_mixin :
    ( ∀ e1 σ1 e2 σ2,
      head_step e1 σ1 e2 σ2 →
      to_val e1 = None
    ) →
    LangEctxMixin to_val head_step ectx.
  Proof.
    assert (ectx_fill_op : ∀ K1 K2 e,
      (K1 ⋅ K2) @@ e = K1 @@ (K2 @@ e)
    ). {
      eauto using fold_left_app.
    }
    assert (ectx_fill_not_val : ∀ K e,
      to_val e = None →
      to_val (K @@ e) = None
    ). {
      induction K as [| k K]; intros; first done.
      naive_solver eauto using IHK, lang_ectxi_mixin_fill_not_val.
    }
    assert (ectx_fill_head_step_val : ∀ K e1 σ1 e2 σ2,
      head_step (K @@ e1) σ1 e2 σ2 →
      is_Some (to_val e1) ∨ K = ∅
    ). {
      induction K as [| k K]; intros * Hstep; first eauto.
      left. edestruct (IHK (k @@ e1)); first done.
      + eauto using lang_ectxi_mixin_fill_val.
      + simplify. cbn in Hstep. eauto using lang_ectxi_mixin_fill_head_step_val.
    }
    econstructor.
    - eauto using lang_ctxi_mixin_ctx_mixin, lang_ectxi_mixin_ctxi_mixin.
    - intros * Heq ? Hstep. revert K_redex Heq.
      induction K as [| k K] using rev_ind; intros K_redex Heq.
      + naive_solver eauto using app_nil_r.
      + destruct K_redex as [| k_redex K_redex _] using rev_ind; intros.
        * cbn in Heq. simplify. eapply ectx_fill_head_step_val in Hstep as [].
          -- exfalso. eapply eq_None_not_Some; eauto.
          -- exists ∅. done.
        * rewrite !ectx_fill_op in Heq.
          assert (k = k_redex) as ->. {
            eapply lang_ectxi_mixin_fill_no_val_inj; [done | | | done];
              eapply ectx_fill_not_val; eauto.
          }
          simplify. destruct IHK with (K_redex := K_redex) as [K' ->]; eauto.
          exists K'. setoid_rewrite app_assoc. eauto.
    - done.
  Qed.
End lang_ectxi_mixin.

Section EctxiLangMixin.
  Context {expr val state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (head_step : expr → state → expr → state → Prop).
  Context (ectxi : Type) `{LangCtxiBase expr ectxi}.

  Record EctxiLangMixin := {
    ectxi_lang_mixin_to_of_val e v :
      e = of_val v →
      to_val e = Some v ;
    ectxi_lang_mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    ectxi_lang_mixin_head_step_not_val e1 σ1 e2 σ2 :
      head_step e1 σ1 e2 σ2 →
      to_val e1 = None ;
    ectxi_lang_mixin_ectxi_mixin :
      LangEctxiMixin to_val head_step ectxi ;
  }.
End EctxiLangMixin.
Global Arguments Build_EctxiLangMixin {_ _ _ _ _ _ _ _} _ _ _ _ : assert.

Structure ectxi_lang := {
  expr : Type ;
  val : Type ;
  state : Type ;
  of_val : val → expr ;
  to_val : expr → option val ;
  head_step : expr → state → expr → state → Prop ;
  ectxi : Type ;
  ectxi_lang_ctxi_base : LangCtxiBase expr ectxi ;
  ectxi_lang_mixin : EctxiLangMixin of_val to_val head_step ectxi ;
}.
Global Arguments Build_ectxi_lang {_ _ _ _ _ _ _ _} _ : assert.
Global Arguments of_val {_} _ : assert.
Global Arguments to_val {_} _ : assert.
Global Arguments head_step {_} _ _ _ _ : assert.
Global Existing Instance ectxi_lang_ctxi_base.

Section ectxi_lang.
  Context {Λ : ectxi_lang}.
  Let ectx := list (ectxi Λ).
  Implicit Types e : expr Λ.
  Implicit Types k : ectxi Λ.
  Implicit Types K : ectx.

  Global Instance ectxi_lang_ectx_empty : Empty ectx :=
    [].
  Global Instance ectxi_lang_ectx_op : Op ectx :=
    flip (++).
  Global Instance ectxi_lang_ectx_fill : Fill ectx (expr Λ) :=
    fold_left (flip (@@)).
  Global Instance ectxi_lang_ectx_base : LangCtxBase (expr Λ) ectx :=
    Build_LangCtxBase _ _ _ _ _.

  Lemma fill_item_not_val k e :
    to_val e = None →
    to_val (k @@ e) = None.
  Proof.
    apply ectxi_lang_mixin.
  Qed.
  Global Instance fill_item_inj k :
    Inj (=) (=) (k @@.).
  Proof.
    apply ectxi_lang_mixin.
  Qed.
  Lemma fill_item_no_val_inj k1 k2 e1 e2 :
    to_val e1 = None →
    to_val e2 = None →
    k1 @@ e1 = k2 @@ e2 →
    k1 = k2.
  Proof.
    apply ectxi_lang_mixin.
  Qed.
  Lemma fill_item_head_step_val k e σ1 e2 σ2 :
    head_step (k @@ e) σ1 e2 σ2 →
    is_Some (to_val e).
  Proof.
    apply ectxi_lang_mixin.
  Qed.

  Lemma fill_item_val k e :
    is_Some (to_val (k @@ e)) →
    is_Some (to_val e).
  Proof.
    rewrite -!not_eq_None_Some. eauto using fill_item_not_val.
  Qed.

  Lemma ectx_lang_of_ectxi_lang_mixin :
    EctxLangMixin of_val to_val head_step ectx.
  Proof.
    econstructor;
      try eapply lang_ectxi_mixin_ectx_mixin;
      eapply ectxi_lang_mixin.
  Qed.
  Canonical ectx_lang_of_ectxi_lang' := Build_ectx_lang ectx_lang_of_ectxi_lang_mixin.
  Canonical lang_of_ectxi_lang' := lang_of_ectx_lang ectx_lang_of_ectxi_lang'.
End ectxi_lang.
Global Arguments ectx_lang_of_ectxi_lang' : clear implicits.
Global Arguments lang_of_ectxi_lang' : clear implicits.
Coercion ectx_lang_of_ectxi_lang' : ectxi_lang >-> ectx_lang.
Coercion lang_of_ectxi_lang' : ectxi_lang >-> lang.

Definition ectx_lang_of_ectxi_lang Λ :=
  let '(@Build_ectxi_lang expr val state of_val to_val head_step ectxi ectxi_fill mix) := Λ in
  @Build_ectx_lang expr val state of_val to_val head_step (list ectxi) _ $
  @ectx_lang_of_ectxi_lang_mixin $
  Build_ectxi_lang mix.
Global Arguments ectx_lang_of_ectxi_lang : simpl never.
