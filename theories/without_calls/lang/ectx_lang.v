From simuliris.common Require Import
  prelude
  tactics.
From simuliris.without_calls Require Export
  lang.lang.

Section LangEctxMixin.
  Context {val expr state : Type}.
  Context (to_val : expr → option val).
  Context (head_step : expr → state → expr → state → Prop).
  Context (ectx : Type) `{LangCtxBase expr ectx}.
  Implicit Types e : expr.
  Implicit Types K : ectx.

  Record LangEctxMixin := {
    lang_ectx_mixin_ctx_mixin :
      LangCtxMixin to_val ectx ;
    lang_ectx_mixin_fill_redex K K_redex e1 e1_redex σ1 e2 σ2 :
      K @@ e1 = K_redex @@ e1_redex →
      to_val e1 = None →
      head_step e1_redex σ1 e2 σ2 →
      ∃ K', K_redex = K ⋅ K' ;
    lang_ectx_mixin_fill_head_step_val K e1 σ1 e2 σ2 :
      head_step (K @@ e1) σ1 e2 σ2 →
      is_Some (to_val e1) ∨ K = ∅ ;
  }.
End LangEctxMixin.
Global Arguments Build_LangEctxMixin {_ _ _ _ _ _ _} _ _ _ : assert.

Section EctxLangMixin.
  Context {expr val state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (head_step : expr → state → expr → state → Prop).
  Context (ectx : Type) `{LangCtxBase expr ectx}.

  Record EctxLangMixin := {
    ectx_lang_mixin_to_of_val e v :
      e = of_val v →
      to_val e = Some v ;
    ectx_lang_mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    ectx_lang_mixin_head_step_not_val e1 σ1 e2 σ2 :
      head_step e1 σ1 e2 σ2 →
      to_val e1 = None ;
    ectx_lang_mixin_ectx_mixin :
      LangEctxMixin to_val head_step ectx ;
  }.
End EctxLangMixin.
Global Arguments Build_EctxLangMixin {_ _ _ _ _ _ _ _} _ _ _ _ : assert.

Structure ectx_lang := {
  expr : Type ;
  val : Type ;
  state : Type ;
  of_val : val → expr ;
  to_val : expr → option val ;
  head_step : expr → state → expr → state → Prop ;
  ectx : Type ;
  ectx_lang_ctx_base : LangCtxBase expr ectx ;
  ectx_lang_mixin : EctxLangMixin of_val to_val head_step ectx ;
}.
Global Arguments Build_ectx_lang {_ _ _ _ _ _ _ _} _ : assert.
Global Arguments of_val {_} _ : assert.
Global Arguments to_val {_} _ : assert.
Global Arguments head_step {_} _ _ _ _ : assert.
Global Existing Instance ectx_lang_ctx_base.

Section ectx_lang.
  Context {Λ : ectx_lang}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  Inductive prim_step e1 σ1 e2 σ2 : Prop :=
    | head_step_fill_prim_step K e1' e2' :
        e1 = K @@ e1' →
        e2 = K @@ e2' →
        head_step e1' σ1 e2' σ2 →
        prim_step e1 σ1 e2 σ2.
  Hint Constructors prim_step : core.

  Definition head_reducible e σ :=
    ∃ e' σ', head_step e σ e' σ'.
  Definition head_irreducible e σ :=
    ∀ e' σ', ¬ head_step e σ e' σ'.
  Definition head_stuck e σ :=
    to_val e = None ∧ head_irreducible e σ.

  Definition sub_redexes_are_values e :=
    ∀ K e',
    e = K @@ e' →
    to_val e' = None →
    K = ∅.

  Class StronglyHeadReducible e :=
    strongly_head_reducible σ : head_reducible e σ.
  Class StronglyHeadIrreducible e :=
    strongly_head_irreducible σ : head_irreducible e σ.
  Class StronglyHeadStuck e := {
    strongly_head_stuck_strongly_head_irreducible :> StronglyHeadIrreducible e ;
    strongly_head_stuck_not_val : to_val e = None ;
    strongly_head_stuck_sub_redexes_are_values : sub_redexes_are_values e ;
  }.

  Record pure_head_step e1 e2 := {
    pure_head_step_safe σ1 :
      head_reducible e1 σ1 ;
    pure_head_step_det σ1 e2' σ2 :
      head_step e1 σ1 e2' σ2 →
      σ2 = σ1 ∧ e2' = e2 ;
  }.
  Class PureHeadExec (ϕ : Prop) n e1 e2 :=
    pure_head_exec : ϕ → nsteps pure_head_step n e1 e2.

  Lemma head_step_not_val e1 σ1 e2 σ2 :
    head_step e1 σ1 e2 σ2 →
    to_val e1 = None.
  Proof.
    apply ectx_lang_mixin.
  Qed.
  Lemma fill_empty e :
    ∅ @@ e = e.
  Proof.
    apply ectx_lang_mixin.
  Qed.
  Lemma fill_op K1 K2 e :
    K1 @@ (K2 @@ e) = (K1 ⋅ K2) @@ e.
  Proof.
    apply ectx_lang_mixin.
  Qed.
  Global Instance fill_inj K :
    Inj (=) (=) (K @@.).
  Proof.
    apply ectx_lang_mixin.
  Qed.
  Lemma fill_not_val K e :
    to_val e = None →
    to_val (K @@ e) = None.
  Proof.
    apply ectx_lang_mixin.
  Qed.
  Lemma fill_redex K K_redex e1 e1_redex σ1 e2 σ2 :
    K @@ e1 = K_redex @@ e1_redex →
    to_val e1 = None →
    head_step e1_redex σ1 e2 σ2 →
    ∃ K', K_redex = K ⋅ K'.
  Proof.
    apply ectx_lang_mixin.
  Qed.
  Lemma fill_head_step_val K e σ1 e2 σ2 :
    head_step (K @@ e) σ1 e2 σ2 →
    is_Some (to_val e) ∨ K = ∅.
  Proof.
    apply ectx_lang_mixin.
  Qed.

  Lemma lang_of_ectx_lang_mixin :
    LangMixin of_val to_val prim_step.
  Proof.
    constructor.
    - apply ectx_lang_mixin.
    - apply ectx_lang_mixin.
    - intros * [? ? ? -> -> ?%head_step_not_val]. eapply fill_not_val. done.
  Qed.
  Canonical lang_of_ectx_lang' := Build_lang lang_of_ectx_lang_mixin.

  Lemma head_step_prim_step e1 σ1 e2 σ2 :
    head_step e1 σ1 e2 σ2 →
    prim_step e1 σ1 e2 σ2.
  Proof.
    econstructor; eauto using fill_empty.
  Qed.
  Lemma prim_step_fill_prim_step K e1 σ1 e2 σ2 :
    prim_step e1 σ1 e2 σ2 →
    prim_step (K @@ e1) σ1 (K @@ e2) σ2.
  Proof.
    intros []. simplify. eauto using fill_op.
  Qed.

  Lemma head_irreducible_not_head_reducible e σ :
    head_irreducible e σ ↔
    ¬ head_reducible e σ.
  Proof.
    rewrite /head_reducible /head_irreducible. naive_solver.
  Qed.
  Lemma reducible_fill_reducible K e σ :
    reducible e σ →
    reducible (K @@ e) σ.
  Proof.
    intros (? & ? & ?). do 2 eexists. eapply prim_step_fill_prim_step. eauto.
  Qed.
  Lemma head_reducible_fill_reducible K e σ :
    head_reducible e σ →
    reducible (K @@ e) σ.
  Proof.
    intros (? & ? & ?). do 2 eexists. eapply head_step_fill_prim_step; eauto.
  Qed.
  Lemma head_reducible_reducible e σ :
    head_reducible e σ →
    reducible e σ.
  Proof.
    rewrite -{2}(fill_empty e). eauto using head_reducible_fill_reducible.
  Qed.
  Lemma reducible_head_reducible e σ :
    reducible e σ →
    sub_redexes_are_values e →
    head_reducible e σ.
  Proof.
    intros (? & ? & []) ?. simplify.
    assert (K = ∅) as -> by eauto using head_step_not_val.
    rewrite fill_empty /head_reducible; eauto.
  Qed.
  Lemma head_irreducible_irreducible e σ :
    head_irreducible e σ →
    sub_redexes_are_values e →
    irreducible e σ.
  Proof.
    rewrite irreducible_not_reducible head_irreducible_not_head_reducible.
    eauto using reducible_head_reducible.
  Qed.
  Lemma head_reducible_fill_prim_step K e1 σ1 e2 σ2 :
    head_reducible e1 σ1 →
    prim_step (K @@ e1) σ1 e2 σ2 →
    ∃ e2', e2 = K @@ e2' ∧ head_step e1 σ1 e2' σ2.
  Proof.
    intros (? & ? & Hstep) [K' e1' e2' Heq -> Hstep'].
    edestruct fill_redex as [K'' ?]; eauto using head_step_not_val.
    simplify. rewrite -fill_op in Heq. simplify.
    exists (K'' @@ e2'). rewrite fill_op; split; first done.
    apply fill_head_step_val in Hstep as [[v ?] | ?].
    { apply head_step_not_val in Hstep'. simplify. }
    simplify. by rewrite !fill_empty.
  Qed.
  Lemma head_reducible_prim_step e1 σ1 e2 σ2 :
    head_reducible e1 σ1 →
    prim_step e1 σ1 e2 σ2 →
    head_step e1 σ1 e2 σ2.
  Proof.
    intros.
    edestruct (head_reducible_fill_prim_step ∅) as (? & ? & ?);
      rewrite ?fill_empty; eauto.
    by simplify; rewrite fill_empty.
  Qed.

  Lemma fill_val K e :
    is_Some (to_val (K @@ e)) →
    is_Some (to_val e).
  Proof.
    rewrite -!not_eq_None_Some. eauto using fill_not_val.
  Qed.
  Lemma fill_prim_step_inv K e1' σ1 e2 σ2 :
    to_val e1' = None →
    prim_step (K @@ e1') σ1 e2 σ2 →
    ∃ e2', e2 = K @@ e2' ∧ prim_step e1' σ1 e2' σ2.
  Proof.
    intros ? [K_redex e1_redex e2_redex Heq -> Hstep].
    edestruct fill_redex as [K' ?]; eauto; simplify.
    rewrite -fill_op in Heq; apply (inj (_ @@.)) in Heq.
    eexists. rewrite -fill_op. eauto.
  Qed.

  Global Instance strongly_head_reducible_strongly_reducible e :
    StronglyHeadReducible e →
    StronglyReducible e.
  Proof.
    intros ? ?. eauto using head_reducible_reducible.
  Qed.
  Global Instance strongly_head_irreducible_strongly_irreducible e :
    StronglyHeadIrreducible e →
    sub_redexes_are_values e →
    StronglyIrreducible e.
  Proof.
    intros ** ?. eauto using head_irreducible_irreducible.
  Qed.
  Global Instance strongly_head_stuck_strongly_stuck e :
    StronglyHeadStuck e →
    StronglyStuck e.
  Proof.
    intros []. econstructor; last done.
    eauto using strongly_head_irreducible_strongly_irreducible.
  Qed.

  Lemma pure_head_step_fill_pure_step K e1 e2 :
    pure_head_step e1 e2 →
    pure_step (K @@ e1) (K @@ e2).
  Proof.
    intros []. econstructor.
    - eauto using head_reducible_fill_reducible.
    - intros * ?%head_reducible_fill_prim_step; naive_solver.
  Qed.
  Lemma pure_head_step_pure_step e1 e2 :
    pure_head_step e1 e2 →
    pure_step e1 e2.
  Proof.
    intros. rewrite -(fill_empty e1) -(fill_empty e2).
    eauto using pure_head_step_fill_pure_step.
  Qed.
  Lemma pure_head_exec_fill_pure_exec K ϕ n e1 e2 :
    PureHeadExec ϕ n e1 e2 →
    PureExec ϕ n (K @@ e1) (K @@ e2).
  Proof.
    intros ? ?.
    eapply nsteps_congruence;
    eauto using pure_head_exec, pure_head_step_fill_pure_step.
  Qed.
  Lemma pure_head_exec_pure_exec ϕ n e1 e2 :
    PureHeadExec ϕ n e1 e2 →
    PureExec ϕ n e1 e2.
  Proof.
    intros. rewrite -(fill_empty e1) -(fill_empty e2).
    eauto using pure_head_exec_fill_pure_exec.
  Qed.

  Global Instance fill_lang_frame K :
    LangFrame (K @@.).
  Proof.
    constructor.
    - apply ectx_lang_mixin.
    - apply prim_step_fill_prim_step.
    - apply fill_prim_step_inv.
  Qed.
End ectx_lang.
Global Arguments lang_of_ectx_lang' : clear implicits.
Coercion lang_of_ectx_lang' : ectx_lang >-> lang.

Definition lang_of_ectx_lang Λ :=
  let '(@Build_ectx_lang expr val state of_val to_val head_step ectx ectx_base mix) := Λ in
  @Build_lang expr val state of_val to_val _ $
  @lang_of_ectx_lang_mixin $
  Build_ectx_lang mix.
Global Arguments lang_of_ectx_lang : simpl never.
