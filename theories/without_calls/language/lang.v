From Coq.Program Require Import
  Equality.

From iris.algebra Require Export
  ofe.

From tmc.common Require Import
  prelude.

Section LangMixin.
  Context {expr val state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (prim_step : expr → state → expr → state → Prop).

  Record LangMixin := {
    lang_mixin_to_of_val v :
      to_val (of_val v) = Some v ;
    lang_mixin_of_to_val e v :
      to_val e = Some v → of_val v = e ;
    lang_mixin_val_stuck e σ e' σ' :
      prim_step e σ e' σ' → to_val e = None ;
  }.
End LangMixin.

Structure lang := {
  expr : Type ;
  val : Type ;
  state : Type ;
  of_val : val → expr ;
  to_val : expr → option val ;
  prim_step : expr → state → expr → state → Prop ;
  lang_mixin : LangMixin of_val to_val prim_step ;
}.
Global Arguments Build_lang {_ _ _ _ _ _} _: assert.
Global Arguments of_val {_} _ : assert.
Global Arguments to_val {_} _ : assert.
Global Arguments prim_step {_} _ _ _ _ : assert.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.

Declare Scope val_scope.
Delimit Scope val_scope with V.
Bind Scope val_scope with val.

Canonical Structure stateO Λ := leibnizO (state Λ).
Canonical Structure valO Λ := leibnizO (val Λ).
Canonical Structure exprO Λ := leibnizO (expr Λ).

Definition cfg (Λ : lang) := (expr Λ * state Λ)%type.

Class LangFrame `(K : expr Λ → expr Λ) := {
  lang_frame_val e :
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

Global Instance language_ctx_id Λ : LangFrame $ @id (expr Λ).
Proof.
  constructor; naive_solver.
Qed.

Section lang.
  Context {Λ : lang}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types ρ : cfg Λ.

  Definition reducible e σ :=
    ∃ e' σ', prim_step e σ e' σ'.
  Definition irreducible e σ :=
    ∀ e' σ', ¬ prim_step e σ e' σ'.
  Definition stuck e σ :=
    to_val e = None ∧ irreducible e σ.
  Definition not_stuck e σ :=
    is_Some (to_val e) ∨ reducible e σ.
  Definition strongly_irreducible e :=
    ∀ σ, irreducible e σ.
  Definition strongly_stuck e :=
    to_val e = None ∧ strongly_irreducible e.

  Inductive step ρ1 ρ2 : Prop :=
    | step_one e1 σ1 e2 σ2 :
        prim_step e1 σ1 e2 σ2 →
        ρ1 = (e1, σ1) →
        ρ2 = (e2, σ2) →
        step ρ1 ρ2.
  Global Arguments step_one {_ _}.

  CoInductive diverge e σ : Prop :=
    | diverge_step e' σ' :
        prim_step e σ e' σ' →
        diverge e' σ' →
        diverge e σ.

  Lemma to_of_val v :
    to_val (of_val v) = Some v.
  Proof.
    apply lang_mixin.
  Qed.
  Lemma of_to_val e v :
    to_val e = Some v →
    of_val v = e.
  Proof.
    apply lang_mixin.
  Qed.
  Lemma of_to_val_flip v e :
    of_val v = e →
    to_val e = Some v.
  Proof.
    intros <-. by rewrite to_of_val.
  Qed.
  Lemma val_stuck e σ e' σ' :
    prim_step e σ e' σ' →
    to_val e = None.
  Proof.
    apply lang_mixin.
  Qed.

  Lemma not_reducible e σ :
    ¬ reducible e σ ↔
    irreducible e σ.
  Proof.
    unfold reducible, irreducible. naive_solver.
  Qed.
  Lemma reducible_not_val e σ :
    reducible e σ →
    to_val e = None.
  Proof.
    intros (? & ? & ?); eauto using val_stuck.
  Qed.
  Lemma val_irreducible e σ :
    is_Some (to_val e) →
    irreducible e σ.
  Proof.
    intros [? ?] ? ? ?%val_stuck. by destruct (to_val e).
  Qed.
  Global Instance of_val_inj :
    Inj (=) (=) (@of_val Λ).
  Proof.
    by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv.
  Qed.
  Lemma not_not_stuck e σ :
    ¬ not_stuck e σ ↔
    stuck e σ.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma strongly_irreducible_irreducible e σ :
    strongly_irreducible e →
    irreducible e σ.
  Proof.
    eauto.
  Qed.
  Lemma strongly_stuck_irreducible e σ :
    strongly_stuck e →
    irreducible e σ.
  Proof.
    intros []. eauto using strongly_irreducible_irreducible.
  Qed.
  Lemma strongly_stuck_stuck e σ :
    strongly_stuck e →
    stuck e σ.
  Proof.
    intros []. split; eauto using strongly_irreducible_irreducible.
  Qed.

  Lemma diverge_reducible e σ :
    diverge e σ →
    reducible e σ.
  Proof.
    intros []. econstructor. eauto.
  Qed.
  Lemma diverge_not_stuck e σ :
    diverge e σ →
    ¬ stuck e σ.
  Proof.
    intros ?%diverge_reducible [? ?%not_reducible]. eauto.
  Qed.
  Lemma diverge_not_strongly_stuck e σ :
    diverge e σ →
    ¬ strongly_stuck e.
  Proof.
    intros ? ?%(strongly_stuck_stuck _ σ). eapply diverge_not_stuck; eauto.
  Qed.
  Lemma diverge_not_val e σ v :
    diverge e σ →
    e ≠ of_val v.
  Proof.
    intros [? ? ? %val_stuck] ?%eq_sym%of_to_val_flip. congruence.
  Qed.

  Lemma rtc_step_val v ρ1 ρ2 :
    rtc step ρ1 ρ2 →
    ρ1.1 = of_val v →
    ρ1 = ρ2.
  Proof.
    intros [| [] ? ? [? ? ? ? ?%val_stuck ? ?]] Heq%eq_sym; simplify_eq; first done.
    eapply of_to_val_flip in Heq. naive_solver.
  Qed.
  Lemma rtc_step_strongly_stuck ρ1 ρ2 :
    rtc step ρ1 ρ2 →
    strongly_stuck ρ1.1 →
    ρ1 = ρ2.
  Proof.
    intros [| [] ? ? []] Hstuck; simplify_eq; first done.
    eapply strongly_stuck_irreducible in Hstuck. rewrite /irreducible in Hstuck.
    naive_solver.
  Qed.

  Section lang_frame.
    Context (K : expr Λ → expr Λ).
    Context `{!LangFrame K}.

    Lemma lang_frame_reducible e σ :
      reducible e σ →
      reducible (K e) σ.
    Proof.
      intros (? & ? & ?).
      repeat eexists. eauto using lang_frame_prim_step.
    Qed.
    Lemma lang_frame_reducible_inv e σ :
      to_val e = None →
      reducible (K e) σ →
      reducible e σ.
    Proof.
      intros ? (? & ? & (? & -> & ?)%lang_frame_prim_step_inv); last done.
      rewrite /reducible. eauto.
    Qed.
    Lemma lang_frame_stuck e σ :
      stuck e σ →
      stuck (K e) σ.
    Proof.
      rewrite /stuck -!not_reducible. intros [].
      split; eauto using lang_frame_val, lang_frame_reducible_inv.
    Qed.
    Lemma lang_frame_strongly_stuck e :
      strongly_stuck e →
      strongly_stuck (K e).
    Proof.
      intros [? ?]. split.
      - eauto using lang_frame_val.
      - intros ?. cut (stuck (K e) σ).
        + rewrite /stuck. naive_solver.
        + apply lang_frame_stuck.
          split; eauto using strongly_irreducible_irreducible.
    Qed.

    Lemma lang_frame_step e1 σ1 e2 σ2 :
      step (e1, σ1) (e2, σ2) →
      step (K e1, σ1) (K e2, σ2).
    Proof.
      intros []. simplify_eq.
      econstructor; auto.
      eauto using lang_frame_prim_step.
    Qed.
    Lemma lang_frame_tc_step e1 σ1 e2 σ2 :
      tc step (e1, σ1) (e2, σ2) →
      tc step (K e1, σ1) (K e2, σ2).
    Proof.
      pose K_cfg : cfg Λ → cfg Λ := λ '(e, σ), (K e, σ).
      change (K ?e, ?σ) with (K_cfg (e, σ)). apply tc_congruence.
      intros [] []. apply lang_frame_step.
    Qed.
    Lemma lang_frame_rtc_step e1 σ1 e2 σ2 :
      rtc step (e1, σ1) (e2, σ2) →
      rtc step (K e1, σ1) (K e2, σ2).
    Proof.
      intros []%rtc_tc; simplify_eq.
      - apply rtc_refl.
      - eauto using tc_rtc, lang_frame_tc_step.
    Qed.
  End lang_frame.

  (* Lemma reducible_fill `{!@LangFrame Λ K} e σ : *)
  (*   reducible e σ → reducible (K e) σ. *)
  (* Proof. *)
  (*   unfold reducible in *. naive_solver eauto using lang_frame_fill_step. *)
  (* Qed. *)
  (* Lemma reducible_fill_inv `{!@LangFrame Λ K} e σ : *)
  (*   to_val e = None → *)
  (*   reducible (K e) σ → *)
  (*   reducible e σ. *)
  (* Proof. *)
  (*   intros ? (e' & σ' & Hstep); unfold reducible. *)
  (*   apply lang_frame_fill_step_inv in Hstep as (e2' & _ & Hstep); eauto. *)
  (* Qed. *)
  (* Lemma irreducible_fill `{!@LangFrame Λ K} e σ : *)
  (*   to_val e = None → *)
  (*   irreducible e σ → *)
  (*   irreducible (K e) σ. *)
  (* Proof. *)
  (*   rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv. *)
  (* Qed. *)
  (* Lemma irreducible_fill_inv `{!@LangFrame Λ K} e σ : *)
  (*   irreducible (K e) σ → irreducible e σ. *)
  (* Proof. *)
  (*   rewrite -!not_reducible. naive_solver eauto using reducible_fill. *)
  (* Qed. *)

  (* Lemma not_stuck_fill_inv K `{!@LangFrame Λ K} e σ : *)
  (*   not_stuck (K e) σ → not_stuck e σ. *)
  (* Proof. *)
  (*   rewrite /not_stuck -!not_eq_None_Some. intros [?|?]. *)
  (*   - auto using lang_frame_fill_not_val. *)
  (*   - destruct (decide (to_val e = None)); eauto using reducible_fill_inv. *)
  (* Qed. *)

  (* Lemma stuck_fill `{!@LangFrame Λ K} e σ : *)
  (*   stuck e σ → stuck (K e) σ. *)
  (* Proof. *)
  (*   rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. *)
  (* Qed. *)

  (* Record pure_step e1 e2 := { *)
  (*   pure_step_safe σ1 : *)
  (*     reducible e1 σ1 ; *)
  (*   pure_step_det σ1 e2' σ2 : *)
  (*     prim_step e1 σ1 e2' σ2 → *)
  (*     σ2 = σ1 ∧ e2' = e2 ; *)
  (* }. *)

  (* Class PureExec (φ : Prop) n e1 e2 := *)
  (*   pure_exec : φ → relations.nsteps pure_step n e1 e2. *)

  (* Lemma pure_step_ctx K `{!@LangFrame Λ K} e1 e2 : *)
  (*   pure_step e1 e2 → *)
  (*   pure_step (K e1) (K e2). *)
  (* Proof. *)
  (*   intros [Hred Hstep]. split. *)
  (*   - unfold reducible in *. naive_solver eauto using lang_frame_fill_step. *)
  (*   - intros σ1 e2' σ2 Hpstep. *)
  (*     destruct (lang_frame_fill_step_inv e1 σ1 e2' σ2) as (e2'' & -> & ?); [|exact Hpstep|]. *)
  (*     + destruct (Hred σ1) as (? & ? & ?); eauto using val_stuck. *)
  (*     + edestruct (Hstep σ1 e2'' σ2) as (? & ->); auto. *)
  (* Qed. *)

  (* Lemma pure_step_nsteps_ctx K `{!@LangFrame Λ K} n e1 e2 : *)
  (*   relations.nsteps pure_step n e1 e2 → *)
  (*   relations.nsteps pure_step n (K e1) (K e2). *)
  (* Proof. *)
  (*   eauto using nsteps_congruence, pure_step_ctx. *)
  (* Qed. *)

  (* Lemma rtc_pure_step_ctx K `{!@LangFrame Λ K} e1 e2 : *)
  (*   rtc pure_step e1 e2 → rtc pure_step (K e1) (K e2). *)
  (* Proof. *)
  (*   eauto using rtc_congruence, pure_step_ctx. *)
  (* Qed. *)

  (* Lemma pure_exec_ctx K `{!@LangFrame Λ K} φ n e1 e2 : *)
  (*   PureExec φ n e1 e2 → *)
  (*   PureExec φ n (K e1) (K e2). *)
  (* Proof. *)
  (*   rewrite /PureExec; eauto using pure_step_nsteps_ctx. *)
  (* Qed. *)

  (* Lemma as_val_is_Some e : *)
  (*   (∃ v, of_val v = e) → is_Some (to_val e). *)
  (* Proof. *)
  (*   intros [v <-]. rewrite to_of_val. eauto. *)
  (* Qed. *)

  (* Lemma prim_step_not_stuck e σ e' σ' : *)
  (*   prim_step e σ e' σ' → not_stuck e σ. *)
  (* Proof. *)
  (*   rewrite /not_stuck /reducible. eauto 10. *)
  (* Qed. *)

  (* Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e : *)
  (*   rtc pure_step (of_val v) e → to_val e = Some v. *)
  (* Proof. *)
  (*   intros ?; rewrite <- to_of_val. *)
  (*   f_equal; symmetry; eapply rtc_nf; first done. *)
  (*   intros [e' [Hstep _]]. *)
  (*   destruct (Hstep inhabitant) as (? & ? & Hval%val_stuck). *)
  (*   by rewrite to_of_val in Hval. *)
  (* Qed. *)
End lang.
