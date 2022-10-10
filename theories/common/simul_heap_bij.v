From iris.base_logic.lib Require Import
  gset_bij.
From iris.base_logic.lib Require Export
  iprop.
From iris.proofmode Require Import
  proofmode.

From simuliris.common Require Export
  bi_typeclasses
  simul_heap.

Class SimulHeapBijGpreS locₜ locₛ valₜ valₛ Σ `{SimulHeapGS locₜ locₛ valₜ valₛ Σ} :=
  simul_heap_bij_GpreS_bij_G : gset_bijG Σ locₜ locₛ.
Local Existing Instance simul_heap_bij_GpreS_bij_G.

Class SimulHeapBijGS locₜ locₛ valₜ valₛ Σ `{SimulHeapGS locₜ locₛ valₜ valₛ Σ} := {
  simul_heap_bij_GS_bij_G : gset_bijG Σ locₜ locₛ ;
  simul_heap_bij_GS_name : gname ;
}.
Arguments Build_SimulHeapBijGS locₜ locₛ valₜ valₛ Σ {_ _ _ _ _ _} _: assert.
Arguments simul_heap_bij_GS_name {_ _ _ _ _ _ _ _ _ _ _} : assert.
Local Existing Instance simul_heap_bij_GS_bij_G.

Section simul_heap_bij.
  Context `{SimulHeapBijGS locₜ locₛ valₜ valₛ Σ}.
  Implicit Types lₜ : locₜ.
  Implicit Types lₛ : locₛ.
  Implicit Types vₜ : valₜ.
  Implicit Types vₛ : valₛ.

  Definition simul_heap_bij_auth (bij : gset (locₜ * locₛ)) :=
    gset_bij_own_auth simul_heap_bij_GS_name (DfracOwn 1) bij.

  Definition simul_heap_bij_elem lₜ lₛ :=
    gset_bij_own_elem simul_heap_bij_GS_name lₜ lₛ.
  Global Instance loc_bi_similar : BiSimilar _ locₜ locₛ :=
    simul_heap_bij_elem.

  Global Instance simul_heap_bij_elem_persistent lₜ lₛ :
    Persistent (lₜ ≈ lₛ).
  Proof.
    apply _.
  Qed.

  Lemma simul_heap_bij_agree lₜ1 lₜ2 lₛ1 lₛ2 :
    lₜ1 ≈ lₛ1 -∗
    lₜ2 ≈ lₛ2 -∗
    ⌜lₜ1 = lₜ2 ↔ lₛ1 = lₛ2⌝.
  Proof.
    iIntros "H1 H2". iApply (gset_bij_own_elem_agree with "H1 H2").
  Qed.
  Lemma simul_heap_bij_func lₜ lₛ1 lₛ2 :
    lₜ ≈ lₛ1 -∗
    lₜ ≈ lₛ2 -∗
    ⌜lₛ1 = lₛ2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (simul_heap_bij_agree with "H1 H2") as "<-"; done.
  Qed.
  Lemma simul_heap_bij_inj lₛ lₜ1 lₜ2 :
    lₜ1 ≈ lₛ -∗
    lₜ2 ≈ lₛ -∗
    ⌜lₜ1 = lₜ2⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (simul_heap_bij_agree with "H1 H2") as "->"; done.
  Qed.

  Section val_similar.
    Context `{BiSimilar (iPropI Σ) valₜ valₛ}.

    Global Instance loc_bi_paired : BiPaired _ locₜ locₛ := (
      λ lₜ lₛ,
        ∃ vₜ vₛ,
        lₜ ↦ₜ vₜ ∗ lₛ ↦ₛ vₛ ∗ vₜ ≈ vₛ
    )%I.

    Definition simul_heap_bij_inv := (
      ∃ bij,
      simul_heap_bij_auth bij ∗
      [∗ set] p ∈ bij, p.1 ⟷ p.2
    )%I.

    Lemma simul_heap_bij_access lₜ lₛ :
      simul_heap_bij_inv -∗
      lₜ ≈ lₛ -∗
      lₜ ⟷ lₛ ∗ (lₜ ⟷ lₛ -∗ simul_heap_bij_inv).
    Proof.
      iIntros "(% & Hauth & Hpairing) #Hsimil".
      iDestruct (gset_bij_elem_of with "[$] [$]") as "%".
      iDestruct (big_sepS_delete with "Hpairing") as "(Hpaired & ?)"; first done.
      iDestruct "Hpaired" as "(% & % & Hpaired)".
      iSplitL "Hpaired"; first by repeat iExists _.
      iIntros. iExists _. iFrame "Hauth".
      iApply big_sepS_delete; [done | by iFrame].
    Qed.

    Lemma simul_heap_bij_insert lₜ lₛ :
      simul_heap_bij_inv -∗
      lₜ ⟷ lₛ ==∗
      simul_heap_bij_inv ∗ lₜ ≈ lₛ.
    Proof.
      iIntros "Hinv (%vₜ & %vₛ & Ht & Hs & Hrel)".
      iDestruct "Hinv" as (bij) "[Hauth Hheap]".
      iAssert ((¬ ⌜set_Exists (λ '(lₜ', lₛ'), lₜ = lₜ') bij⌝)%I) as "%Hextₜ".
      { iIntros (([lₜ' lₛ'] & Hin & <-)).
        iPoseProof (big_sepS_elem_of with "Hheap") as (vₜ' vₛ') "(Hcon & _ & _)".
        { eapply Hin. }
        iPoseProof (simul_mapstoₜ_valid_2  with "Ht Hcon") as "%Hcon"; exfalso.
        destruct Hcon as [Hcon _]. by apply dfrac_valid_own_r in Hcon.
      }
      iAssert ((¬ ⌜set_Exists (λ '(lₜ', lₛ'), lₛ = lₛ') bij⌝)%I) as "%Hextₛ".
      { iIntros (([lₜ' lₛ'] & Hin & <-)).
        iPoseProof (big_sepS_elem_of with "Hheap") as (vₜ' vₛ') "(_ & Hcon & _)".
        { eapply Hin. }
        iPoseProof (simul_mapstoₛ_valid_2 with "Hs Hcon") as "%Hcon"; exfalso.
        destruct Hcon as [Hcon _]. by apply dfrac_valid_own_r in Hcon.
      }
      iMod ((gset_bij_own_extend lₜ lₛ) with "Hauth") as "[Hinv #Helem]".
      - intros lₛ' Hlₛ'. apply Hextₜ. by exists (lₜ, lₛ').
      - intros lₜ' Hlₜ'. apply Hextₛ. by exists (lₜ', lₛ).
      - iModIntro. iSplitL; last done.
        iExists _. iFrame.
        iApply big_sepS_insert. { contradict Hextₜ. by exists (lₜ, lₛ). }
        iFrame. iExists vₜ, vₛ. iFrame.
    Qed.
  End val_similar.
End simul_heap_bij.

Section init.
  Context `{SimulHeapBijGpreS locₜ locₛ valₜ valₛ Σ}.
  Context `{BiSimilar (iPropI Σ) valₜ valₛ}.

  Lemma simul_heap_bij_init_names :
    ⊢ |==> ∃ γ : gname,
      let _ := Build_SimulHeapBijGS locₜ locₛ valₜ valₛ Σ γ in
      simul_heap_bij_inv.
  Proof.
    iMod (gset_bij_own_alloc_empty) as (γ) "Hinv".
    iExists γ. iModIntro. iExists (∅). iSplitL "Hinv"; first by iApply "Hinv".
    by iApply big_sepS_empty.
  Qed.

  Lemma simul_heap_bij_init :
    ⊢ |==> ∃ _ : SimulHeapBijGS locₜ locₛ valₜ valₛ Σ,
      simul_heap_bij_inv.
  Proof.
    iMod (simul_heap_bij_init_names) as (γ) "Hinit".
    iModIntro. iExists (Build_SimulHeapBijGS _ _ _ _ _ γ). iFrame.
  Qed.
End init.
