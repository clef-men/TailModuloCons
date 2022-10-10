From iris.proofmode Require Import
  proofmode.

From simuliris.common Require Export
  simul_heap_bij.
From simuliris.without_calls Require Export
  simul.
From simuliris.without_calls.tmc Require Export
  lang.tactics.

Notation "'SIM' eₜ '≲' eₛ '{{' Φ } }" := (simul Φ eₜ%V%E eₛ%V%E)
( at level 70,
  eₜ, eₛ, Φ at level 200,
  format "'[hv' 'SIM'  '[' eₜ ']'  '/  ' ≲  '[' eₛ ']'  '/  ' {{  '[' Φ ']'  '/  ' } } ']'"
) : bi_scope.

Notation "'{{{' P } } } eₜ ≲ eₛ {{{ Φ } } }" := (□ (P -∗ SIM eₜ ≲ eₛ {{ Φ }}))%I
( at level 20,
  P, eₜ, eₛ, Φ at level 200,
  format "'[hv' {{{  '[' P ']'  } } }  '/  ' '[' eₜ ']'  '/' ≲  '[' eₛ ']'  '/' {{{  '[' Φ ']'  } } } ']'"
) : bi_scope.

Class TmcSimulHeapGS Σ := {
  tmc_simul_heap_bij_GS_heap_GS :> SimulHeapGS loc loc val val Σ ;
  tmc_simul_heap_bij_GS_heap_bij_GS :> SimulHeapBijGS loc loc val val Σ ;
}.

Section tmc_simul_heap.
  Context `{TmcSimulHeapGS Σ}.
  Implicit Types blk blkₜ blkₛ : block.
  Implicit Types l lₜ lₛ : loc.
  Implicit Types v vₜ vₛ : val.
  Implicit Types vs vsₜ vsₛ : val * val.

  Global Instance block_bi_mapstoₜ : BiMapstoₜ _ block (val * val) := (
    λ blk dq '(v1, v2),
      (blk, 𝟙) ↦ₜ{dq} v1 ∗ (blk, 𝟚) ↦ₜ{dq} v2
  )%I.
  Global Instance block_bi_mapstoₛ : BiMapstoₛ _ block (val * val) := (
    λ blk dq '(v1, v2),
      (blk, 𝟙) ↦ₛ{dq} v1 ∗ (blk, 𝟚) ↦ₛ{dq} v2
  )%I.

  Global Instance loc_bi_similar : BiSimilar _ loc loc :=
    simul_heap_bij_elem.
  Global Instance block_bi_similar : BiSimilar _ block block := (
    λ blkₜ blkₛ,
      (blkₜ, 𝟙) ≈ (blkₛ, 𝟙) ∗ (blkₜ, 𝟚) ≈ (blkₛ, 𝟚)
  )%I.
  Global Instance val_bi_similar : BiSimilar _ val val := (
    λ vₜ vₛ,
      match vₜ, vₛ with
      | Block blkₜ, Block blkₛ => blkₜ ≈ blkₛ
      | Index iₜ, Index iₛ => ⌜iₜ = iₛ⌝
      | Unit, Unit => True
      | _, _ => False
      end
  )%I.

  Global Instance block_bi_paired : BiPaired _ block block := (
    λ blkₜ blkₛ,
      (blkₜ, 𝟙) ⟷ (blkₛ, 𝟙) ∗ (blkₜ, 𝟚) ⟷ (blkₛ, 𝟚)
  )%I.

  Global Instance tmc_simul_GS : SimulGS _ tmc_lang tmc_lang := (
    λ σₜ σₛ,
      simul_heap_interpₜ σₜ ∗
      simul_heap_interpₛ σₛ ∗
      simul_heap_bij_inv
  )%I.
  Global Instance tmc_simul : Simul (iPropI Σ) expr expr :=
    _.

  Global Instance loc_bi_similar_persistent lₜ lₛ :
    Persistent (lₜ ≈ lₛ).
  Proof.
    apply _.
  Qed.
  Global Instance block_bi_similar_persistent blkₜ blkₛ :
    Persistent (blkₜ ≈ blkₛ).
  Proof.
    apply _.
  Qed.
  Global Instance val_bi_similar_persistent vₜ vₛ :
    Persistent (vₜ ≈ vₛ).
  Proof.
    destruct vₜ, vₛ; apply _.
  Qed.
  Global Instance vals_bi_similar_persistent vsₜ vsₛ :
    Persistent (vsₜ ≈ vsₛ).
  Proof.
    destruct vsₜ, vsₛ. apply _.
  Qed.

  Lemma simul_heap_allocₜ σₜ σₛ l v :
    l ∉ σₜ →
    simul_state_interp σₜ σₛ ==∗
    simul_state_interp (<[l := v]> σₜ) σₛ ∗ l ↦ₜ v.
  Proof.
    iIntros (?%eq_None_not_Some) "(? & ? & ?)".
    iMod (simul_heap_allocₜ with "[$]") as "(? & ?)"; first done. iModIntro.
    iFrame.
  Qed.
  Lemma simul_heap_allocₛ σₜ σₛ l v :
    l ∉ σₛ →
    simul_state_interp σₜ σₛ ==∗
    simul_state_interp σₜ (<[l := v]> σₛ) ∗ l ↦ₛ v.
  Proof.
    iIntros (?%eq_None_not_Some) "(? & ? & ?)".
    iMod (simul_heap_allocₛ with "[$]") as "(? & ?)"; first done. iModIntro.
    iFrame.
  Qed.
  Lemma simul_heap_alloc_blockₜ σₜ σₛ blk vs :
    blk ∉ σₜ →
    simul_state_interp σₜ σₛ ==∗
    simul_state_interp (<[blk := vs]> σₜ) σₛ ∗ blk ↦ₜ vs.
  Proof.
    destruct vs as [v1 v2]. iIntros.
    iMod (simul_heap_allocₜ _ _ (blk, 𝟙) with "[$]") as "(? & ?)".
    { eauto with tmc_lang. }
    iMod (simul_heap_allocₜ _ _ (blk, 𝟚) with "[$]") as "(? & ?)".
    { eauto with tmc_lang. }
    iModIntro. iFrame.
  Qed.
  Lemma simul_heap_alloc_blockₛ σₜ σₛ blk vs :
    blk ∉ σₛ →
    simul_state_interp σₜ σₛ ==∗
    simul_state_interp σₜ (<[blk := vs]> σₛ) ∗ blk ↦ₛ vs.
  Proof.
    destruct vs as [v1 v2]. iIntros.
    iMod (simul_heap_allocₛ _ _ (blk, 𝟙) with "[$]") as "(? & ?)".
    { eauto with tmc_lang. }
    iMod (simul_heap_allocₛ _ _ (blk, 𝟚) with "[$]") as "(? & ?)".
    { eauto with tmc_lang. }
    iModIntro. iFrame.
  Qed.

  Lemma simul_heap_alloc_bigₜ σₜ σₜ' σₛ :
    σₜ' ##ₘ σₜ →
    simul_state_interp σₜ σₛ ==∗
    simul_state_interp (σₜ' ∪ σₜ) σₛ ∗ ([∗ map] l ↦ v ∈ σₜ', l ↦ₜ v).
  Proof.
    iIntros "% (? & ? & ?)".
    iMod (simul_heap_alloc_bigₜ with "[$]") as "(? & ?)"; first done. iModIntro.
    iFrame.
  Qed.
  Lemma simul_heap_alloc_bigₛ σₜ σₛ σₛ' :
    σₛ' ##ₘ σₛ →
    simul_state_interp σₜ σₛ ==∗
    simul_state_interp σₜ (σₛ' ∪ σₛ) ∗ ([∗ map] l ↦ v ∈ σₛ', l ↦ₛ v).
  Proof.
    iIntros "% (? & ? & ?)".
    iMod (simul_heap_alloc_bigₛ with "[$]") as "(? & ?)"; first done. iModIntro.
    iFrame.
  Qed.

  Lemma simul_heap_validₜ σₜ σₛ l dq v :
    simul_state_interp σₜ σₛ -∗
    l ↦ₜ{dq} v -∗
    ⌜σₜ !! l = Some v⌝.
  Proof.
    iIntros "(? & ? & ?) ?".
    iDestruct (simul_heap_validₜ with "[$] [$]") as "%". done.
  Qed.
  Lemma simul_heap_validₛ σₜ σₛ l dq v :
    simul_state_interp σₜ σₛ -∗
    l ↦ₛ{dq} v -∗
    ⌜σₛ !! l = Some v⌝.
  Proof.
    iIntros "(? & ? & ?) ?".
    iDestruct (simul_heap_validₛ with "[$] [$]") as "%". done.
  Qed.
  Lemma simul_heap_valid_blockₜ σₜ σₛ blk dq vs :
    simul_state_interp σₜ σₛ -∗
    blk ↦ₜ{dq} vs -∗
    ⌜σₜ !! blk = Some vs⌝.
  Proof.
    destruct vs as [v1 v2]. iIntros "? (? & ?)".
    iDestruct (simul_heap_validₜ _ _ (blk, 𝟙) with "[$] [$]") as "%".
    iDestruct (simul_heap_validₜ _ _ (blk, 𝟚) with "[$] [$]") as "%".
    eauto with tmc_lang.
  Qed.
  Lemma simul_heap_valid_blockₛ σₜ σₛ blk dq vs :
    simul_state_interp σₜ σₛ -∗
    blk ↦ₛ{dq} vs -∗
    ⌜σₛ !! blk = Some vs⌝.
  Proof.
    destruct vs as [v1 v2]. iIntros "? (? & ?)".
    iDestruct (simul_heap_validₛ _ _ (blk, 𝟙) with "[$] [$]") as "%".
    iDestruct (simul_heap_validₛ _ _ (blk, 𝟚) with "[$] [$]") as "%".
    eauto with tmc_lang.
  Qed.

  Lemma simul_heap_updateₜ σₜ σₛ l v :
    simul_state_interp σₜ σₛ -∗
    l ↦ₜ- ==∗
    simul_state_interp (<[l := v]> σₜ) σₛ ∗ l ↦ₜ v.
  Proof.
    iIntros "(? & ? & ?) ?".
    iMod (simul_heap_updateₜ with "[$] [$]") as "(? & ?)". iModIntro.
    iFrame.
  Qed.
  Lemma simul_heap_updateₛ σₜ σₛ l v :
    simul_state_interp σₜ σₛ -∗
    l ↦ₛ- ==∗
    simul_state_interp σₜ (<[l := v]> σₛ) ∗ l ↦ₛ v.
  Proof.
    iIntros "(? & ? & ?) ?".
    iMod (simul_heap_updateₛ with "[$] [$]") as "(? & ?)". iModIntro.
    iFrame.
  Qed.
  Lemma simul_heap_update_blockₜ σₜ σₛ blk vs :
    simul_state_interp σₜ σₛ -∗
    blk ↦ₜ- ==∗
    simul_state_interp (<[blk := vs]> σₜ) σₛ ∗ blk ↦ₜ vs.
  Proof.
    iIntros "? (%vs' & Hblk)".
    destruct vs as [v1 v2], vs' as [v1' v2']. iDestruct "Hblk" as "(Hblk1 & Hblk2)".
    iMod (simul_heap_updateₜ _ _ (blk, 𝟙) with "[$] [Hblk1]") as "(? & ?)".
    { by iExists _. }
    iMod (simul_heap_updateₜ _ _ (blk, 𝟚) with "[$] [Hblk2]") as "(? & ?)".
    { by iExists _. }
    iModIntro. iFrame.
  Qed.
  Lemma simul_heap_update_blockₛ σₜ σₛ blk vs :
    simul_state_interp σₜ σₛ -∗
    blk ↦ₛ- ==∗
    simul_state_interp σₜ (<[blk := vs]> σₛ) ∗ blk ↦ₛ vs.
  Proof.
    iIntros "? (%vs' & Hblk)".
    destruct vs as [v1 v2], vs' as [v1' v2']. iDestruct "Hblk" as "(Hblk1 & Hblk2)".
    iMod (simul_heap_updateₛ _ _ (blk, 𝟙) with "[$] [Hblk1]") as "(? & ?)".
    { by iExists _. }
    iMod (simul_heap_updateₛ _ _ (blk, 𝟚) with "[$] [Hblk2]") as "(? & ?)".
    { by iExists _. }
    iModIntro. iFrame.
  Qed.

  Lemma simul_heap_bij_valid σₜ σₛ lₜ lₛ :
    simul_state_interp σₜ σₛ -∗
    lₜ ≈ lₛ -∗
      ∃ vₜ vₛ,
      ⌜σₜ !! lₜ = Some vₜ⌝ ∗ ⌜σₛ !! lₛ = Some vₛ⌝ ∗ vₜ ≈ vₛ.
  Proof.
    iIntros "(? & ? & ?) ?".
    iDestruct (simul_heap_bij_access with "[$] [$]") as "((% & % & ? & ? & ?) & ?)".
    iDestruct (simul_heap.simul_heap_validₜ with "[$] [$]") as "%".
    iDestruct (simul_heap.simul_heap_validₛ with "[$] [$]") as "%".
    eauto.
  Qed.
  Lemma simul_heap_bij_valid_block σₜ σₛ blkₜ blkₛ :
    simul_state_interp σₜ σₛ -∗
    blkₜ ≈ blkₛ -∗
      ∃ vsₜ vsₛ,
      ⌜σₜ !! blkₜ = Some vsₜ⌝ ∗ ⌜σₛ !! blkₛ = Some vsₛ⌝ ∗ vsₜ ≈ vsₛ.
  Proof.
    iIntros "? (? & ?)".
    iDestruct (simul_heap_bij_valid _ _ (_, 𝟙) with "[$] [$]") as
      (vₜ1 vₛ1) "#(% & % & ?)".
    iDestruct (simul_heap_bij_valid _ _ (_, 𝟚) with "[$] [$]") as
      (vₜ2 vₛ2) "#(% & % & ?)".
    unfold_state_eqns. iExists (vₜ1, vₜ2), (vₛ1, vₛ2).
    repeat iSplit; eauto with tmc_lang.
  Qed.

  Lemma simul_heap_bij_access σₜ σₛ lₜ lₛ :
    simul_state_interp σₜ σₛ -∗
    lₜ ≈ lₛ -∗
    lₜ ⟷ lₛ ∗ (lₜ ⟷ lₛ -∗ simul_state_interp σₜ σₛ).
  Proof.
    iIntros "(? & ? & ?) ?".
    iDestruct (simul_heap_bij_access with "[$] [$]") as "(? & ?)".
    iFrame. done.
  Qed.

  Lemma simul_heap_bij_insert σₜ σₛ lₜ lₛ :
    simul_state_interp σₜ σₛ -∗
    lₜ ⟷ lₛ ==∗
    simul_state_interp σₜ σₛ ∗ lₜ ≈ lₛ.
  Proof.
    iIntros "(? & ? & ?) ?".
    iMod (simul_heap_bij_insert with "[$] [$]") as "(? & ?)". iModIntro.
    iFrame.
  Qed.
  Lemma simul_heap_bij_insert_block σₜ σₛ blkₜ blkₛ :
    simul_state_interp σₜ σₛ -∗
    blkₜ ⟷ blkₛ ==∗
    simul_state_interp σₜ σₛ ∗ blkₜ ≈ blkₛ.
  Proof.
    iIntros "? (? & ?)".
    iMod (simul_heap_bij_insert with "[$] [$]") as "(? & ?)".
    iMod (simul_heap_bij_insert with "[$] [$]") as "(? & ?)".
    iModIntro. iFrame.
  Qed.

  Lemma simul_heap_bij_update σₜ σₛ lₜ lₛ vₜ vₛ :
    simul_state_interp σₜ σₛ -∗
    lₜ ≈ lₛ -∗
    vₜ ≈ vₛ ==∗
    simul_state_interp (<[lₜ := vₜ]> σₜ) (<[lₛ := vₛ]> σₛ).
  Proof.
    iIntros "(? & ? & ?) **".
    iDestruct (simul_heap_bij.simul_heap_bij_access with "[$] [$]") as
      "((%vₜ' & %vₛ' & Hlₜ & Hlₛ & ?) & Hinv)".
    iMod (simul_heap.simul_heap_updateₜ with "[$] [Hlₜ]") as "(? & ?)".
    { by iExists _. }
    iMod (simul_heap.simul_heap_updateₛ with "[$] [Hlₛ]") as "(? & ?)".
    { by iExists _. }
    iModIntro. iFrame. iApply "Hinv". repeat iExists _. iFrame. done.
  Qed.
  Lemma simul_heap_bij_update_block σₜ σₛ blkₜ blkₛ vsₜ vsₛ :
    simul_state_interp σₜ σₛ -∗
    blkₜ ≈ blkₛ -∗
    vsₜ ≈ vsₛ ==∗
    simul_state_interp (<[blkₜ := vsₜ]> σₜ) (<[blkₛ := vsₛ]> σₛ).
  Proof.
    destruct vsₜ as [vₜ1 vₜ2], vsₛ as [vₛ1 vₛ2].
    iIntros "? (? & ?) (? & ?)".
    iMod (simul_heap_bij_update _ _ (_, 𝟙) _ vₜ1 with "[$] [$] [$]").
    iMod (simul_heap_bij_update _ _ (_, 𝟚) _ vₜ2 with "[$] [$] [$]").
    done.
  Qed.
End tmc_simul_heap.
