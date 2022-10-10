From iris.proofmode Require Import
  coq_tactics
  reduction.
From iris.proofmode Require Export
  proofmode.

From simuliris.common Require Import
  prelude.
From simuliris.without_calls.tmc Require Export
  simul.rules.

Ltac reshape_expr e cb :=
  let rec go K e :=
    let go k e := go (k :: K) e in
    match e with
    | Let ?e1 ?e2 => go (EctxLet e2) e1
    | Match ?e0 ?e1 ?e2 => go (EctxMatch e1 e2) e0
    | Store ?e1 ?e2 ?e3 => go (EctxStore1 e2 e3) e1
    | Store (Val ?v1) ?e2 ?e3 => go (EctxStore2 v1 e3) e2
    | Store (Val ?v1) (Val ?v2) ?e3 => go (EctxStore3 v1 v2) e3
    | _ => cb K e
    end
  in
  go (@empty ectxi _) e.

Section tmc_simul_heap.
  Context `{TmcSimulHeapGS Σ}.
  Implicit Types blk blkₜ blkₛ : block.
  Implicit Types v vₜ vₛ : val.
  Implicit Types e eₜ eₛ : expr.
  Implicit Types K Kₜ Kₛ : ectx.
  Implicit Types Φ : expr → expr → iProp Σ.

  Lemma tac_simul_bupd eₜ eₛ Φ Δ :
    envs_entails Δ (SIM eₜ ≲ eₛ {{ |==> Φ }})%I →
    envs_entails Δ (SIM eₜ ≲ eₛ {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => ->.
    iApply simul_bupd.
  Qed.
  Lemma tac_bupd_simul eₜ eₛ Φ Δ :
    envs_entails Δ (|==> SIM eₜ ≲ eₛ {{ Φ }}) →
    envs_entails Δ (SIM eₜ ≲ eₛ {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => ->.
    iApply bupd_simul.
  Qed.

  Lemma tac_simul_strongly_stuck eₜ eₛ Φ Δ :
    StronglyStuck eₜ →
    StronglyStuck eₛ →
    envs_entails Δ (SIM eₜ ≲ eₛ {{ Φ }}).
  Proof.
    rewrite envs_entails_eq.
    iIntros. iApply simul_strongly_stuck.
  Qed.

  Lemma tac_simul_post eₜ eₛ Φ Δ :
    envs_entails Δ (Φ eₜ eₛ) →
    envs_entails Δ (SIM eₜ ≲ eₛ {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => ->.
    iIntros. iApply simul_post. done.
  Qed.

  Lemma tac_simul_bind Kₜ Kₛ fₜ fₛ eₜ eₛ Φ Δ :
    fₜ = (λ eₜ, Kₜ @@ eₜ) →
    fₛ = (λ eₛ, Kₛ @@ eₛ) →
    envs_entails Δ (SIM eₜ ≲ eₛ {{ λ eₜ' eₛ', SIM fₜ eₜ' ≲ fₛ eₛ' {{ Φ }} }})%I →
    envs_entails Δ (SIM Kₜ @@ eₜ ≲ Kₛ @@ eₛ {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => -> -> ->. rewrite simul_bind //.
  Qed.

  Lemma tac_simul_pure_execₜ ϕ n eₜ1 eₜ2 eₛ Φ Δ :
    PureExec ϕ n eₜ1 eₜ2 →
    ϕ →
    envs_entails Δ (SIM eₜ2 ≲ eₛ {{ Φ }}) →
    envs_entails Δ (SIM eₜ1 ≲ eₛ {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => ? ? ->. rewrite simul_pure_execₜ //.
  Qed.
  Lemma tac_simul_pure_execₛ ϕ n eₜ eₛ1 eₛ2 Φ Δ :
    PureExec ϕ n eₛ1 eₛ2 →
    ϕ →
    envs_entails Δ (SIM eₜ ≲ eₛ2 {{ Φ }}) →
    envs_entails Δ (SIM eₜ ≲ eₛ1 {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => ? ? ->. rewrite simul_pure_execₛ //.
  Qed.

  Lemma tac_simul_pairₜ eₜ1 eₜ2 eₛ Φ Δ :
    envs_entails Δ (
      SIM let: eₜ1 in let: eₜ2.[ren (+1)] in ⟨&1, &0⟩ ≲ eₛ {{ Φ }} ∗
      SIM let: eₜ2 in let: eₜ1.[ren (+1)] in ⟨&0, &1⟩ ≲ eₛ {{ Φ }}
    ) →
    envs_entails Δ (SIM (eₜ1, eₜ2) ≲ eₛ {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => ->.
    iIntros "(? & ?)". iApply (simul_pairₜ with "[$] [$]").
  Qed.
  Lemma tac_simul_pairₛ1 eₜ eₛ1 eₛ2 Φ Δ :
    envs_entails Δ (SIM eₜ ≲ let: eₛ1 in let: eₛ2.[ren (+1)] in ⟨&1, &0⟩ {{ Φ }}) →
    envs_entails Δ (SIM eₜ ≲ (eₛ1, eₛ2) {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => ->. rewrite simul_pairₛ1 //.
  Qed.
  Lemma tac_simul_pairₛ2 eₜ eₛ1 eₛ2 Φ Δ :
    envs_entails Δ (SIM eₜ ≲ let: eₛ2 in let: eₛ1.[ren (+1)] in ⟨&0, &1⟩ {{ Φ }}) →
    envs_entails Δ (SIM eₜ ≲ (eₛ1, eₛ2) {{ Φ }}).
  Proof.
    rewrite envs_entails_eq => ->. rewrite simul_pairₛ2 //.
  Qed.

  Lemma tac_simul_pair_detₜ id vₜ1 vₜ2 eₛ Φ Δ :
    ( ∀ blkₜ,
      match envs_app false (Esnoc Enil id (blkₜ ↦ₜ (vₜ1, vₜ2))) Δ with
      | Some Δ' => envs_entails Δ' (SIM blkₜ ≲ eₛ {{ Φ }})
      | None => False
      end
    ) →
    envs_entails Δ (SIM ⟨vₜ1, vₜ2⟩ ≲ eₛ {{ Φ }}).
  Proof.
    rewrite envs_entails_eq -simul_pair_detₜ => HΔ.
    iIntros. specialize (HΔ blkₜ).
    destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    iApply HΔ. iApply (envs_app_sound with "[$]"); naive_solver.
  Qed.
  Lemma tac_simul_pair_detₛ id eₜ vₛ1 vₛ2 Φ Δ :
    ( ∀ blkₛ,
      match envs_app false (Esnoc Enil id (blkₛ ↦ₛ (vₛ1, vₛ2))) Δ with
      | Some Δ' => envs_entails Δ' (SIM eₜ ≲ blkₛ {{ Φ }})
      | None => False
      end
    ) →
    envs_entails Δ (SIM eₜ ≲ ⟨vₛ1, vₛ2⟩ {{ Φ }}).
  Proof.
    rewrite envs_entails_eq -simul_pair_detₛ => HΔ.
    iIntros. specialize (HΔ blkₛ).
    destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    iApply HΔ. iApply (envs_app_sound with "[$]"); naive_solver.
  Qed.

  Lemma tac_simul_match_block blkₜ eₜ1 eₜ2 blkₛ eₛ1 eₛ2 Φ :
    blkₜ ≈ blkₛ -∗
    ( ∀ vₜ1 vₜ2 vₛ1 vₛ2,
      (vₜ1, vₜ2) ≈ (vₛ1, vₛ2) -∗
      SIM eₜ2.[#vₜ2, #vₜ1/] ≲ eₛ2.[#vₛ2, #vₛ1/] {{ Φ }}
    ) -∗
    SIM match: blkₜ with () => eₜ1 | _ => eₜ2 end
      ≲ match: blkₛ with () => eₛ1 | _ => eₛ2 end
      {{ Φ }}.
  Proof.

Lemma tac_target_red_loadsc Δ i K b l q v Ψ:
  envs_lookup i Δ = Some (b, l ↦t{#q} v)%I →
  envs_entails Δ (target_red (fill K (Val v)) Ψ) →
  envs_entails Δ (target_red (fill K (Load ScOrd (LitV l))) Ψ).

  Lemma tac_simul_storeₜ blkₜ iₜ vₜ eₛ Φ :
    (blkₜ, iₜ) ↦ₜ- -∗
    ((blkₜ, iₜ) ↦ₜ vₜ -∗ SIM () ≲ eₛ {{ Φ }}) -∗
    SIM blkₜ .# iₜ <- vₜ ≲ eₛ {{ Φ }}.
  Proof.
  Qed.
  Lemma tac_simul_storeₛ eₜ blkₛ iₛ vₛ Φ :
    (blkₛ, iₛ) ↦ₛ- -∗
    ((blkₛ, iₛ) ↦ₛ vₛ -∗ SIM eₜ ≲ () {{ Φ }}) -∗
    SIM eₜ ≲ blkₛ .# iₛ <- vₛ {{ Φ }}.
  Proof.
  Qed.
End tmc_simul_heap.
