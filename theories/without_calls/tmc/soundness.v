From simuliris.common Require Import
  prelude
  tactics.
From simuliris.without_calls Require Export
  refinement.
From simuliris.without_calls.tmc Require Import
  simul.proofmode
  simul.csimul.
From simuliris.without_calls.tmc Require Export
  transformation.

Implicit Types blk blkₜ blkₛ : block.
Implicit Types i iₜ iₛ : index.
Implicit Types l lₜ lₛ : loc.
Implicit Types v vₜ vₛ : val.
Implicit Types e eₜ eₛ : expr.

Section tmc_simul_heap.
  Context `{TmcSimulHeapGS Σ}.

  Definition simul_post_dps l eₜ eₛ := (
    ∃ vₜ vₛ,
    ⌜eₜ = #()⌝ ∗ ⌜eₛ = vₛ⌝ ∗ l ↦ₜ vₜ ∗ vₜ ≈ vₛ
  )%I.

  Definition tmc_dir_spec' eₛ eₜ :=
    well_formed eₛ →
    ⊢ CSIM eₜ ≲ eₛ {{ simul_post_val }}.
  Definition tmc_dir_spec eₛ eₜ :=
    tmc_dir eₛ eₜ →
    tmc_dir_spec' eₛ eₜ.
  Definition tmc_dps_spec' blkₜ i eₛ eₜ :=
    well_formed eₛ →
    (blkₜ, i) ↦ₜ- -∗
    CSIM eₜ ≲ eₛ {{ simul_post_dps (blkₜ, i) }}.
  Definition tmc_dps_spec blkₜ i eₛ eₜ :=
    tmc_dps blkₜ i eₛ eₜ →
    tmc_dps_spec' blkₜ i eₛ eₜ.
  Definition tmc_spec eₛ eₜ :=
    tmc_dir_spec eₛ eₜ ∧
    ∀ blkₜ i, tmc_dps_spec blkₜ i eₛ eₜ.

  Lemma tmc_sound' eₛ eₜ :
    tmc_dir_spec eₛ eₜ.
  Proof.
    cut (tmc_spec eₛ eₜ). { rewrite /tmc_spec. naive_solver. }
    revert eₜ. induction eₛ as [eₛ IHeₛ] using (well_founded_ind subexpr_wf).
    cut (
      ( ∀ eₛ eₜ,
        tmc_dir eₛ eₜ →
        (∀ eₛ' eₜ', eₛ' ⊏ eₛ → tmc_spec eₛ' eₜ') →
        tmc_dir_spec' eₛ eₜ
      ) ∧ (
        ∀ (dst idx : expr) eₛ eₜ,
        tmc_dps dst idx eₛ eₜ →
        (∀ eₛ' eₜ', eₛ' ⊏ eₛ → tmc_spec eₛ' eₜ') →
        ∃ blkₜ i, dst = blkₜ ∧ idx = i ∧ tmc_dps_spec' blkₜ i eₛ eₜ
      )
    ). {
      rewrite {3}/tmc_spec /tmc_dir_spec /tmc_dps_spec /tmc_dir_spec' /tmc_dps_spec'.
      naive_solver.
    }
    clear eₛ IHeₛ. apply tmc_ind.
    -
  Qed.
End tmc_simul_heap.

Lemma tmc_sound eₜ eₛ :
  well_formed eₛ →
  tmc_dir eₛ eₜ →
  eₜ ⊴ eₛ.
Proof.
Qed.
