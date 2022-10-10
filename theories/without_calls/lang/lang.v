From iris.algebra Require Export
  ofe
  cmra. (* Op *)

From simuliris.common Require Import
  prelude
  tactics.
From simuliris.common Require Export
  typeclasses.

Class LangCtxBase expr ctx := {
  lang_ctx_empty :> Empty ctx ;
  lang_ctx_op :> Op ctx ;
  lang_ctx_fill :> Fill ctx expr ;
}.

Section LangCtxMixin.
  Context {val expr : Type}.
  Context (to_val : expr → option val).
  Context (ctx : Type) `{LangCtxBase expr ctx}.
  Implicit Types e : expr.
  Implicit Types C : ctx.

  Record LangCtxMixin := {
    lang_ctx_mixin_fill_empty e :
      ∅ @@ e = e ;
    lang_ctx_mixin_fill_op C1 C2 e :
      C1 @@ (C2 @@ e) = (C1 ⋅ C2) @@ e ;
    lang_ctx_mixin_fill_inj C :
      Inj (=) (=) (C @@.) ;
    lang_ctx_mixin_fill_not_val C e :
      to_val e = None →
      to_val (C @@ e) = None ;
  }.
End LangCtxMixin.
Global Arguments Build_LangCtxMixin {_ _ _ _ _} _ _ _ _ : assert.

Class LangCtxiBase expr ctxi :=
  lang_ctxi_fill :> Fill ctxi expr.

Section LangCtxiMixin.
  Context {val expr : Type}.
  Context (to_val : expr → option val).
  Context ctxi `{LangCtxiBase expr ctxi}.
  Implicit Types e : expr .
  Implicit Types c : ctxi.

  Record LangCtxiMixin := {
    lang_ctxi_mixin_fill_inj c :
      Inj (=) (=) (c @@.) ;
    lang_ctxi_mixin_fill_not_val c e :
      to_val e = None →
      to_val (c @@ e) = None ;
  }.
End LangCtxiMixin.
Global Arguments Build_LangCtxiMixin {_ _ _ _ _} _ _ : assert.

Section lang_ctxi_mixin.
  Context {val expr : Type}.
  Context {to_val : expr → option val}.
  Context `{LangCtxiBase expr ctxi}.
  Context (lang_ctxi_mixin : LangCtxiMixin to_val ctxi).

  Lemma lang_ctxi_mixin_fill_val k e :
    is_Some (to_val (k @@ e)) →
    is_Some (to_val e).
  Proof.
    rewrite -!not_eq_None_Some. eauto using lang_ctxi_mixin_fill_not_val.
  Qed.

  Let ctx := list ctxi.

  Global Instance lang_ctxi_mixin_ctx_empty : Empty ctx :=
    [].
  Global Instance lang_ctxi_mixin_ctx_op : Op ctx :=
    flip (++).
  Global Instance lang_ctxi_mixin_ctx_fill : Fill ctx expr :=
    fold_left (flip (@@)).
  Global Instance lang_ctxi_mixin_ctx_base : LangCtxBase expr ctx :=
    Build_LangCtxBase _ _ _ _ _.

  Lemma lang_ctxi_mixin_ctx_mixin :
    LangCtxMixin to_val ctx.
  Proof.
    econstructor.
    - done.
    - simpl. eauto using fold_left_app.
    - induction C as [| c C]; intros ?**; first eauto.
      unshelve eapply (inj (c @@.)); eauto using lang_ctxi_mixin_fill_inj.
    - induction C; naive_solver eauto using lang_ctxi_mixin_fill_not_val.
  Qed.
End lang_ctxi_mixin.

Section LangMixin.
  Context {expr val state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (prim_step : expr → state → expr → state → Prop).

  Record LangMixin := {
    lang_mixin_to_of_val e v :
      e = of_val v →
      to_val e = Some v ;
    lang_mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    lang_mixin_prim_step_not_val e1 σ1 e2 σ2 :
      prim_step e1 σ1 e2 σ2 →
      to_val e1 = None ;
  }.
End LangMixin.
Global Arguments Build_LangMixin {_ _ _ _ _ _} _ _ _ : assert.

Structure lang := {
  expr : Type ;
  val : Type ;
  state : Type ;
  of_val : val → expr ;
  to_val : expr → option val ;
  prim_step : expr → state → expr → state → Prop ;
  lang_mixin : LangMixin of_val to_val prim_step ;
}.
Global Arguments Build_lang {_ _ _ _ _ _} _ : assert.
Global Arguments of_val {_} _ : assert.
Global Arguments to_val {_} _ : assert.
Global Arguments prim_step {_} _ _ _ _ : assert.

Definition cfg Λ := (expr Λ * state Λ)%type.

Canonical Structure stateO Λ := leibnizO (state Λ).
Canonical Structure valO Λ := leibnizO (val Λ).
Canonical Structure exprO Λ := leibnizO (expr Λ).

Class LangCtx Λ ctx := {
  lang_ctx_base :> LangCtxBase (expr Λ) ctx ;
  lang_ctx_mixin : LangCtxMixin to_val ctx ;
}.
Global Arguments Build_LangCtx {_ _ _} _ : assert.

Class LangCtxi Λ ctxi := {
  lang_ctxi_base :> LangCtxiBase (expr Λ) ctxi ;
  lang_ctxi_mixin : LangCtxiMixin to_val ctxi ;
}.
Global Arguments Build_LangCtxi {_ _ _} _ : assert.

Program Global Instance lang_ctxi_ctx `{LangCtxi Λ ctxi} : LangCtx Λ (list ctxi) :=
  Build_LangCtx _.
Next Obligation.
  eauto using lang_ctxi_mixin_ctx_mixin, lang_ctxi_mixin.
Qed.

Class LangFrame {Λ : lang} (K : expr Λ → expr Λ) := {
  lang_frame_not_val e :
    to_val e = None →
    to_val (K e) = None ;
  lang_frame_prim_step e1 σ1 e2 σ2 :
    prim_step e1 σ1 e2 σ2 →
    prim_step (K e1) σ1 (K e2) σ2 ;
  lang_frame_prim_step_inv e1' σ1 e2 σ2 :
    to_val e1' = None →
    prim_step (K e1') σ1 e2 σ2 →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 e2' σ2 ;
}.

Global Instance lang_frame_id Λ :
  LangFrame (@id (expr Λ)).
Proof.
  constructor; naive_solver.
Qed.

Section lang.
  Context {Λ : lang}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types ρ : cfg Λ.

  Inductive step ρ1 ρ2 : Prop :=
    | prim_step_step e1 σ1 e2 σ2 :
        prim_step e1 σ1 e2 σ2 →
        ρ1 = (e1, σ1) →
        ρ2 = (e2, σ2) →
        step ρ1 ρ2.
  Global Arguments prim_step_step {_ _}.
  Hint Constructors step : core.

  Definition reducible e σ :=
    ∃ e' σ', prim_step e σ e' σ'.
  Definition irreducible e σ :=
    ∀ e' σ', ¬ prim_step e σ e' σ'.
  Definition stuck e σ :=
    irreducible e σ ∧ to_val e = None.

  Class StronglyReducible e :=
    strongly_reducible σ : reducible e σ.
  Class StronglyIrreducible e :=
    strongly_irreducible σ : irreducible e σ.
  Class StronglyStuck e := {
    strongly_stuck_strongly_irreducible :> StronglyIrreducible e ;
    strongly_stuck_not_val : to_val e = None ;
  }.

  Definition converges e σ e' σ' :=
    rtc step (e, σ) (e', σ') ∧ irreducible e' σ'.

  CoInductive diverges e σ : Prop :=
    | diverges_step e' σ' :
        prim_step e σ e' σ' →
        diverges e' σ' →
        diverges e σ.

  Record pure_step e1 e2 := {
    pure_step_safe σ1 :
      reducible e1 σ1 ;
    pure_step_det σ1 e2' σ2 :
      prim_step e1 σ1 e2' σ2 →
      σ2 = σ1 ∧ e2' = e2 ;
  }.
  Class PureExec (ϕ : Prop) n e1 e2 :=
    pure_exec : ϕ → nsteps pure_step n e1 e2.

  Lemma to_of_val e v :
    e = of_val v →
    to_val e = Some v.
  Proof.
    apply lang_mixin.
  Qed.
  Lemma of_to_val e v :
    to_val e = Some v →
    of_val v = e.
  Proof.
    apply lang_mixin.
  Qed.
  Lemma prim_step_not_val e1 σ1 e2 σ2 :
    prim_step e1 σ1 e2 σ2 →
    to_val e1 = None.
  Proof.
    apply lang_mixin.
  Qed.

  Lemma step_prim_step e1 σ1 e2 σ2 :
    step (e1, σ1) (e2, σ2) →
    prim_step e1 σ1 e2 σ2.
  Proof.
    intros []. simplify. eauto.
  Qed.
  Lemma irreducible_not_reducible e σ :
    irreducible e σ ↔
    ¬ reducible e σ.
  Proof.
    rewrite /reducible /irreducible. naive_solver.
  Qed.
  Lemma reducible_not_val e σ :
    reducible e σ →
    to_val e = None.
  Proof.
    intros (? & ? & ?); eauto using prim_step_not_val.
  Qed.
  Lemma val_irreducible e v σ :
    e = of_val v →
    irreducible e σ.
  Proof.
    intros ?%to_of_val ? ? ?%prim_step_not_val. naive_solver.
  Qed.
  Lemma stuck_irreducible e σ :
    stuck e σ →
    irreducible e σ.
  Proof.
    rewrite /stuck. naive_solver.
  Qed.
  Lemma stuck_not_val e σ :
    stuck e σ →
    to_val e = None.
  Proof.
    rewrite /stuck. naive_solver.
  Qed.

  Lemma diverges_reducible e σ :
    diverges e σ →
    reducible e σ.
  Proof.
    intros []. econstructor. eauto.
  Qed.
  Lemma diverges_not_stuck e σ :
    diverges e σ →
    ¬ stuck e σ.
  Proof.
    by intros ?%diverges_reducible ?%stuck_irreducible%irreducible_not_reducible.
  Qed.
  Lemma diverges_not_val e σ v :
    diverges e σ →
    e ≠ of_val v.
  Proof.
    intros [? ? ? %prim_step_not_val] ?%to_of_val. naive_solver.
  Qed.

  Lemma strongly_stuck_stuck e σ :
    StronglyStuck e →
    stuck e σ.
  Proof.
    intros []. econstructor; done.
  Qed.

  Lemma pure_step_prim_step e1 e2 σ :
    pure_step e1 e2 →
    prim_step e1 σ e2 σ.
  Proof.
    intros [(? & ? & Hstep) Hdet].
    specialize (Hdet _ _ _ Hstep). simplify. eauto.
  Qed.
  Lemma pure_steps_pure_exec n e1 e2 :
    nsteps pure_step n e1 e2 →
    PureExec True n e1 e2.
  Proof.
    intros ? ?. done.
  Qed.
  Lemma pure_step_pure_exec e1 e2 :
    pure_step e1 e2 →
    PureExec True 1 e1 e2.
  Proof.
    intros. eapply pure_steps_pure_exec, nsteps_once. done.
  Qed.

  Lemma rtc_step_val v ρ1 ρ2 :
    rtc step ρ1 ρ2 →
    ρ1.1 = of_val v →
    ρ1 = ρ2.
  Proof.
    intros [| [] ? ? [? ? ? ? ?%prim_step_not_val ? ?]] ?%to_of_val;
      simplify; naive_solver.
  Qed.
  Lemma rtc_step_stuck ρ1 ρ2 :
    rtc step ρ1 ρ2 →
    stuck ρ1.1 ρ1.2 →
    ρ1 = ρ2.
  Proof.
    intros [| [] ? ? []] Hstuck; simplify; first done.
    eapply stuck_irreducible in Hstuck. rewrite /irreducible in Hstuck.
    naive_solver.
  Qed.

  Section lang_frame.
    Context (K : expr Λ → expr Λ) `{!LangFrame K}.

    Lemma lang_frame_step e1 σ1 e2 σ2 :
      step (e1, σ1) (e2, σ2) →
      step (K e1, σ1) (K e2, σ2).
    Proof.
      intros []. simplify.
      econstructor; auto. eauto using lang_frame_prim_step.
    Qed.
    Lemma lang_frame_reducible e σ :
      reducible e σ →
      reducible (K e) σ.
    Proof.
      rewrite /reducible. naive_solver eauto using lang_frame_prim_step.
    Qed.
    Lemma lang_frame_tc_step e1 σ1 e2 σ2 :
      tc step (e1, σ1) (e2, σ2) →
      tc step (K e1, σ1) (K e2, σ2).
    Proof.
      set K_cfg : cfg Λ → cfg Λ := λ '(e, σ), (K e, σ).
      change (K ?e, ?σ) with (K_cfg (e, σ)). apply tc_congruence.
      intros [] []. apply lang_frame_step.
    Qed.
    Lemma lang_frame_rtc_step e1 σ1 e2 σ2 :
      rtc step (e1, σ1) (e2, σ2) →
      rtc step (K e1, σ1) (K e2, σ2).
    Proof.
      intros []%rtc_tc; simplify; eauto using rtc_refl, tc_rtc, lang_frame_tc_step.
    Qed.

    Lemma lang_frame_reducible_inv e σ :
      to_val e = None →
      reducible (K e) σ →
      reducible e σ.
    Proof.
      intros ? (? & ? & (? & -> & ?)%lang_frame_prim_step_inv); last done.
      rewrite /reducible. eauto.
    Qed.
    Lemma lang_frame_irreducible e σ :
      to_val e = None →
      irreducible e σ →
      irreducible (K e) σ.
    Proof.
      rewrite !irreducible_not_reducible. eauto using lang_frame_reducible_inv.
    Qed.
    Lemma lang_frame_stuck e σ :
      stuck e σ →
      stuck (K e) σ.
    Proof.
      rewrite /stuck. intros [].
      split; eauto using lang_frame_not_val, lang_frame_irreducible.
    Qed.

    Lemma lang_frame_pure_step e1 e2 :
      pure_step e1 e2 →
      pure_step (K e1) (K e2).
    Proof.
      intros []. econstructor.
      - eauto using lang_frame_reducible.
      - intros * Hstep. eapply lang_frame_prim_step_inv in Hstep; first naive_solver.
        unshelve eauto using reducible_not_val; eauto.
    Qed.
    Lemma lang_frame_pure_exec ϕ n e1 e2 :
      PureExec ϕ n e1 e2 →
      PureExec ϕ n (K e1) (K e2).
    Proof.
      intros ? ?. eapply nsteps_congruence; eauto using lang_frame_pure_step.
    Qed.
  End lang_frame.
End lang.
