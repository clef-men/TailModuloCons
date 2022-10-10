From iris.proofmode Require Import
  proofmode.

From simuliris.common Require Import
  prelude.
From simuliris.without_calls.tmc Require Import
  simul.simul.

Definition bisubst := var → val * val.
Notation "Γ .ₜ" := (fst ∘ Γ) (at level 5, format "Γ .ₜ").
Notation "Γ .ₛ" := (snd ∘ Γ) (at level 5, format "Γ .ₛ").
Notation "Γ .ₜ#" := (of_val ∘ Γ.ₜ) (at level 5, format "Γ .ₜ#").
Notation "Γ .ₛ#" := (of_val ∘ Γ.ₛ) (at level 5, format "Γ .ₛ#").

Section tmc_simul_heap.
  Context `{TmcSimulHeapGS Σ}.
  Implicit Types Γ : bisubst.

  Global Instance bisubst_bi_well_formed : BiWellFormed _ bisubst := (
    λ Γ,
      ∀ x, (Γ x).1 ≈ (Γ x).2
  )%I.

  Definition ground_bisubst : bisubst :=
    λ _, ((), ())%V.
  Lemma ground_bisubst_well_formed :
    ⊢ bi_well_formed ground_bisubst.
  Proof.
    iIntros. done.
  Qed.
End tmc_simul_heap.
