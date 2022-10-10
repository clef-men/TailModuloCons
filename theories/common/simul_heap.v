From iris.bi Require Import
  lib.fractional.
From iris.base_logic Require Import
  lib.gen_heap.
From iris.proofmode Require Import
  proofmode.

From simuliris.common Require Export
  bi_typeclasses.

Class SimulHeapGS locₜ locₛ valₜ valₛ Σ `{Countable locₛ, Countable locₜ} := {
  simul_heap_GS_heap_GSₜ : gen_heapGS locₜ valₜ Σ ;
  simul_heap_GS_heap_GSₛ : gen_heapGS locₛ valₛ Σ ;
}.
Global Arguments Build_SimulHeapGS _ _ _ _ _ {_ _ _ _ _ _} : assert.

Notation simul_heap_interpₜ σ := (gen_heap_interp (hG := simul_heap_GS_heap_GSₜ) σ).
Notation simul_heap_interpₛ σ := (gen_heap_interp (hG := simul_heap_GS_heap_GSₛ) σ).

Global Instance simul_bi_mapstoₜ `{SimulHeapGS locₜ locₛ valₜ valₛ Σ}
: BiMapstoₜ (iPropI Σ) locₜ valₜ
:= mapsto (hG := simul_heap_GS_heap_GSₜ).
Global Instance simul_bi_mapstoₛ `{SimulHeapGS locₜ locₛ valₜ valₛ Σ}
: BiMapstoₛ (iPropI Σ) locₛ valₛ
:= mapsto (hG := simul_heap_GS_heap_GSₛ).

Section simul_heap.
  Context `{SimulHeapGS locₜ locₛ valₜ valₛ Σ}.

  Global Instance simul_mapstoₜ_timeless l dq v :
    Timeless (l ↦ₜ{dq} v).
  Proof.
    apply _.
  Qed.
  Global Instance simul_mapstoₛ_timeless l dq v :
    Timeless (l ↦ₛ{dq} v).
  Proof.
    apply _.
  Qed.

  Global Instance simul_mapstoₜ_fractional l v :
    Fractional (λ q, l ↦ₜ{#q} v)%I.
  Proof.
    apply _.
  Qed.
  Global Instance simul_mapstoₛ_fractional l v :
    Fractional (λ q, l ↦ₛ{#q} v)%I.
  Proof.
    apply _.
  Qed.

  Global Instance simul_mapstoₜ_as_fractional l q v :
    AsFractional (l ↦ₜ{#q} v) (λ q, l ↦ₜ{#q} v)%I q.
  Proof.
    apply _.
  Qed.
  Global Instance simul_mapstoₛ_as_fractional l q v :
    AsFractional (l ↦ₛ{#q} v) (λ q, l ↦ₛ{#q} v)%I q.
  Proof.
    apply _.
  Qed.

  Global Instance simul_mapstoₜ_persistent l v :
    Persistent (l ↦ₜ□ v).
  Proof.
    apply _.
  Qed.
  Global Instance simul_mapstoₛ_persistent l v :
    Persistent (l ↦ₛ□ v).
  Proof.
    apply _.
  Qed.

  Lemma simul_mapstoₜ_valid l dq v :
    l ↦ₜ{dq} v -∗
    ⌜✓ dq⌝%Qp.
  Proof.
    eauto using mapsto_valid.
  Qed.
  Lemma simul_mapstoₛ_valid l dq v :
    l ↦ₛ{dq} v -∗
    ⌜✓ dq⌝%Qp.
  Proof.
    eauto using mapsto_valid.
  Qed.

  Lemma simul_mapstoₜ_valid_2 l dq1 dq2 v1 v2 :
    l ↦ₜ{dq1} v1 -∗
    l ↦ₜ{dq2} v2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    eauto using mapsto_valid_2.
  Qed.
  Lemma simul_mapstoₛ_valid_2 l dq1 dq2 v1 v2 :
    l ↦ₛ{dq1} v1 -∗
    l ↦ₛ{dq2} v2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    eauto using mapsto_valid_2.
  Qed.

  Lemma simul_mapstoₜ_agree l dq1 dq2 v1 v2 :
    l ↦ₜ{dq1} v1 -∗
    l ↦ₜ{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    eauto using mapsto_agree.
  Qed.
  Lemma simul_mapstoₛ_agree l dq1 dq2 v1 v2 :
    l ↦ₛ{dq1} v1 -∗
    l ↦ₛ{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    eauto using mapsto_agree.
  Qed.

  Lemma simul_mapstoₜ_combine l dq1 dq2 v1 v2 :
    l ↦ₜ{dq1} v1 -∗
    l ↦ₜ{dq2} v2 -∗
    l ↦ₜ{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    eauto using mapsto_combine.
  Qed.
  Lemma simul_mapstoₛ_combine l dq1 dq2 v1 v2 :
    l ↦ₛ{dq1} v1 -∗
    l ↦ₛ{dq2} v2 -∗
    l ↦ₛ{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    eauto using mapsto_combine.
  Qed.

   Lemma simul_mapstoₜ_frac_ne l1 l2 dq1 dq2 v1 v2 :
    ¬ ✓(dq1 ⋅ dq2) →
    l1 ↦ₜ{dq1} v1 -∗
    l2 ↦ₜ{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
   Proof.
     eauto using mapsto_frac_ne.
   Qed.
   Lemma simul_mapstoₛ_frac_ne l1 l2 dq1 dq2 v1 v2 :
    ¬ ✓(dq1 ⋅ dq2) →
    l1 ↦ₛ{dq1} v1 -∗
    l2 ↦ₛ{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
   Proof.
     eauto using mapsto_frac_ne.
   Qed.

   Lemma simul_mapstoₜ_ne l1 l2 dq2 v1 v2 :
     l1 ↦ₜ v1 -∗
     l2 ↦ₜ{dq2} v2 -∗
     ⌜l1 ≠ l2⌝.
   Proof.
     eauto using mapsto_ne.
   Qed.
   Lemma simul_mapstoₛ_ne l1 l2 dq2 v1 v2 :
     l1 ↦ₛ v1 -∗
     l2 ↦ₛ{dq2} v2 -∗
     ⌜l1 ≠ l2⌝.
   Proof.
     eauto using mapsto_ne.
   Qed.

   Lemma simul_mapstoₜ_persist l dq v :
     l ↦ₜ{dq} v ==∗
     l ↦ₜ□ v.
   Proof.
     eauto using mapsto_persist.
   Qed.
   Lemma simul_mapstoₛ_persist l dq v :
     l ↦ₛ{dq} v ==∗
     l ↦ₛ□ v.
   Proof.
     eauto using mapsto_persist.
   Qed.

  Lemma simul_heap_allocₜ σ l v :
    σ !! l = None →
    simul_heap_interpₜ σ ==∗
    simul_heap_interpₜ (<[l := v]> σ) ∗ l ↦ₜ v.
  Proof.
    iIntros.
    iMod (gen_heap_alloc with "[$]") as "(? & ? & _)"; first done. iModIntro.
    iFrame.
  Qed.
  Lemma simul_heap_allocₛ σ l v :
    σ !! l = None →
    simul_heap_interpₛ σ ==∗
    simul_heap_interpₛ (<[l := v]> σ) ∗ l ↦ₛ v.
  Proof.
    iIntros.
    iMod (gen_heap_alloc with "[$]") as "(? & ? & _)"; first done. iModIntro.
    iFrame.
  Qed.

  Lemma simul_heap_alloc_bigₜ σ σ' :
    σ' ##ₘ σ →
    simul_heap_interpₜ σ ==∗
    simul_heap_interpₜ (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ₜ v).
  Proof.
    iIntros.
    iMod (gen_heap_alloc_big σ σ' with "[$]") as "(? & ? & _)"; first done. iModIntro.
    iFrame.
  Qed.
  Lemma simul_heap_alloc_bigₛ σ σ' :
    σ' ##ₘ σ →
    simul_heap_interpₛ σ ==∗
    simul_heap_interpₛ (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ₛ v).
  Proof.
    iIntros.
    iMod (gen_heap_alloc_big σ σ' with "[$]") as "(? & ? & _)"; first done. iModIntro.
    iFrame.
  Qed.

  Lemma simul_heap_validₜ σ l dq v :
    simul_heap_interpₜ σ -∗
    l ↦ₜ{dq} v -∗
    ⌜σ !! l = Some v⌝.
  Proof.
    eauto using gen_heap_valid.
  Qed.
  Lemma simul_heap_validₛ σ l dq v :
    simul_heap_interpₛ σ -∗
    l ↦ₛ{dq} v -∗
    ⌜σ !! l = Some v⌝.
  Proof.
    eauto using gen_heap_valid.
  Qed.

  Lemma simul_heap_updateₜ σ l v :
    simul_heap_interpₜ σ -∗
    l ↦ₜ- ==∗
    simul_heap_interpₜ (<[l := v]> σ) ∗ l ↦ₜ v.
  Proof.
    iIntros "? (% & ?)". iApply (gen_heap_update with "[$] [$]").
  Qed.
  Lemma simul_heap_updateₛ σ l v :
    simul_heap_interpₛ σ -∗
    l ↦ₛ- ==∗
    simul_heap_interpₛ (<[l := v]> σ) ∗ l ↦ₛ v.
  Proof.
    iIntros "? (% & ?)". iApply (gen_heap_update with "[$] [$]").
  Qed.
End simul_heap.

Lemma simul_heap_init `{gen_heapGpreS locₜ valₜ Σ, gen_heapGpreS locₛ valₛ Σ} σₜ σₛ :
  ⊢ |==> ∃ _ : SimulHeapGS locₜ locₛ valₜ valₛ Σ,
    simul_heap_interpₜ σₜ ∗ ([∗ map] lₜ ↦ vₜ ∈ σₜ, lₜ ↦ₜ vₜ) ∗
    simul_heap_interpₛ σₛ ∗ ([∗ map] lₛ ↦ vₛ ∈ σₛ, lₛ ↦ₛ vₛ).
Proof.
  iMod (gen_heap_init_names σₜ) as (? ?) "(? & ? & ?)".
  iMod (gen_heap_init_names σₛ) as (? ?) "(? & ? & ?)".
  iExists (Build_SimulHeapGS _ _ _ _ _).
  iModIntro. iFrame.
Qed.
