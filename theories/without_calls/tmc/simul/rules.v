From iris.proofmode Require Import
  proofmode.

From simuliris.common Require Import
  prelude
  tactics.
From simuliris.without_calls.tmc Require Export
  lang.tactics
  simul.simul.

Implicit Types blk blkₜ blkₛ : block.
Implicit Types i iₜ iₛ : index.
Implicit Types v vₜ vₛ : val.
Implicit Types e eₜ eₛ : expr.

Section strongly_head_reducible.
  Local Ltac solve :=
    intros ?**; eauto with tmc_lang.

  Global Instance strongly_head_reducible_pair e1 e2 :
    StronglyHeadReducible (e1, e2)%E.
  Proof.
    solve.
  Qed.
  Global Instance strongly_head_reducible_pair_det v1 v2 :
    StronglyHeadReducible ⟨v1, v2⟩%E.
  Proof.
    solve.
  Qed.
End strongly_head_reducible.

Section strongly_head_irreducible.
  Local Ltac solve :=
    intros ** ?** ?** Hstep; invert Hstep; eauto.

  Global Instance strongly_head_irreducible_fail :
    StronglyHeadIrreducible fail%E.
  Proof.
    solve.
  Qed.
  Global Instance strongly_head_irreducible_match_index i e1 e2 :
    StronglyHeadIrreducible match: i with () => e1 | _ => e2 end%E.
  Proof.
    solve.
  Qed.
  Global Instance strongly_head_irreducible_store_no_block v1 v2 v3 :
    ¬ (∃ blk, v1 = Block blk) →
    StronglyHeadIrreducible (v1 .# v2 <- v3)%E.
  Proof.
    solve.
  Qed.
  Global Instance strongly_head_irreducible_store_no_index v1 v2 v3 :
    ¬ (∃ i, v2 = Index i) →
    StronglyHeadIrreducible (v1 .# v2 <- v3)%E.
  Proof.
    solve.
  Qed.
End strongly_head_irreducible.

Section strongly_head_stuck.
  Local Ltac solve :=
    intros; econstructor;
    typeclasses eauto with core tmc_lang typeclass_instances.

  Global Instance strongly_head_stuck_fail :
    StronglyHeadStuck fail%E.
  Proof.
    solve.
  Qed.
  Global Instance strongly_head_stuck_match_index i e1 e2 :
    StronglyHeadStuck match: i with () => e1 | _ => e2 end%E.
  Proof.
    solve.
  Qed.
  Global Instance strongly_head_stuck_store_no_block v1 v2 v3 :
    ¬ (∃ blk, v1 = Block blk) →
    StronglyHeadStuck (v1 .# v2 <- v3)%E.
  Proof.
    solve.
  Qed.
  Global Instance strongly_head_stuck_store_no_index v1 v2 v3 :
    ¬ (∃ i, v2 = Index i) →
    StronglyHeadStuck (v1 .# v2 <- v3)%E.
  Proof.
    solve.
  Qed.
End strongly_head_stuck.

Section pure_exec.
  Local Ltac solve :=
    eapply pure_head_exec_pure_exec;
    intros ?; eapply nsteps_once; econstructor;
    [ eauto with tmc_lang
    | intros; invert_head_step; eauto
    ].

  Global Instance pure_exec_let v e :
    PureExec True 1 (let: #v in e)%E e.[#v/].
  Proof.
    solve.
  Qed.
  Global Instance pure_exec_match_unit e1 e2 :
    PureExec True 1 (Match (Val Unit) e1 e2) e1.
  Proof.
    solve.
  Qed.
End pure_exec.

Section tmc_simul_heap.
  Context `{TmcSimulHeapGS Σ}.
  Implicit Types Φ : expr → expr → iProp Σ.

  (* Lemma simul_letₜ vₜ eₜ eₛ Φ : *)
  (*   SIM eₜ.[#vₜ/] ≲ eₛ {{ Φ }} -∗ *)
  (*   SIM let: vₜ in eₜ ≲ eₛ {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros. iApply simul_pure_execₜ; done. *)
  (* Qed. *)
  (* Lemma simul_letₛ eₜ vₛ eₛ Φ : *)
  (*   SIM eₜ ≲ eₛ.[#vₛ/] {{ Φ }} -∗ *)
  (*   SIM eₜ ≲ let: vₛ in eₛ {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros. iApply simul_pure_execₛ; done. *)
  (* Qed. *)

  (* Lemma simul_match_unitₜ eₜ1 eₜ2 eₛ Φ : *)
  (*   SIM eₜ1 ≲ eₛ {{ Φ }} -∗ *)
  (*   SIM match: () with () => eₜ1 | _ => eₜ2 end ≲ eₛ {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros. iApply simul_pure_execₜ; done. *)
  (* Qed. *)
  (* Lemma simul_match_unitₛ eₜ eₛ1 eₛ2 Φ : *)
  (*   SIM eₜ ≲ eₛ1 {{ Φ }} -∗ *)
  (*   SIM eₜ ≲ match: () with () => eₛ1 | _ => eₛ2 end {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros. iApply simul_pure_execₛ; done. *)
  (* Qed. *)

  Lemma simul_pairₜ eₜ1 eₜ2 eₛ Φ :
    SIM let: eₜ1 in let: eₜ2.[ren (+1)] in ⟨&1, &0⟩ ≲ eₛ {{ Φ }} -∗
    SIM let: eₜ2 in let: eₜ1.[ren (+1)] in ⟨&0, &1⟩ ≲ eₛ {{ Φ }} -∗
    SIM (eₜ1, eₜ2) ≲ eₛ {{ Φ }}.
  Proof.
    iIntros. iApply simul_head_stepₜ. iIntros. iModIntro.
    iSplit; first eauto with tmc_lang.
    iIntros. iModIntro. invert_head_step; iFrame.
  Qed.
  Lemma simul_pairₛ1 eₜ eₛ1 eₛ2 Φ :
    SIM eₜ ≲ let: eₛ1 in let: eₛ2.[ren (+1)] in ⟨&1, &0⟩ {{ Φ }} -∗
    SIM eₜ ≲ (eₛ1, eₛ2) {{ Φ }}.
  Proof.
    iIntros. iApply simul_head_stepₛ. iIntros. iModIntro.
    repeat iExists _. iFrame. iPureIntro. econstructor.
  Qed.
  Lemma simul_pairₛ2 eₜ eₛ1 eₛ2 Φ :
    SIM eₜ ≲ let: eₛ2 in let: eₛ1.[ren (+1)] in ⟨&0, &1⟩ {{ Φ }} -∗
    SIM eₜ ≲ (eₛ1, eₛ2) {{ Φ }}.
  Proof.
    iIntros. iApply simul_head_stepₛ. iIntros. iModIntro.
    repeat iExists _. iFrame. iPureIntro. econstructor.
  Qed.

  Lemma simul_pair_detₜ vₜ1 vₜ2 eₛ Φ :
    (∀ blkₜ, blkₜ ↦ₜ (vₜ1, vₜ2) -∗ SIM blkₜ ≲ eₛ {{ Φ }}) -∗
    SIM ⟨vₜ1, vₜ2⟩ ≲ eₛ {{ Φ }}.
  Proof.
    iIntros "H". iApply simul_head_stepₜ. iIntros. iModIntro.
    iSplit; first eauto with tmc_lang. iIntros. invert_head_step.
    iMod (simul_heap_alloc_blockₜ with "[$]") as "(? & ?)"; first done.
    iModIntro. iFrame. iApply "H". iFrame.
  Qed.
  Lemma simul_pair_detₛ eₜ vₛ1 vₛ2 Φ :
    (∀ blkₛ, blkₛ ↦ₛ (vₛ1, vₛ2) -∗ SIM eₜ ≲ blkₛ {{ Φ }}) -∗
    SIM eₜ ≲ ⟨vₛ1, vₛ2⟩ {{ Φ }}.
  Proof.
    iIntros "H". iApply simul_head_stepₛ. iIntros.
    set blk := fresh σₛ.
    iMod (simul_heap_alloc_blockₛ _ _ blk with "[$]") as "(? & ?)".
    { eauto with tmc_lang. }
    iModIntro. repeat iExists _. iSplit; first (simpl; eauto with tmc_lang).
    iFrame. iApply "H". iFrame.
  Qed.

  Lemma simul_pair_unitₜ1 eₜ eₛ :
    □ (SIM eₜ ≲ eₛ {{ simul_post_val }}) -∗
    SIM (eₜ, ())
      ≲ eₛ
      {{ λ eₜ' eₛ',
          ∃ blkₜ vₜ vₛ,
          ⌜eₜ' = blkₜ⌝ ∗ ⌜eₛ' = vₛ⌝ ∗ blkₜ ↦ₜ (vₜ, ()%V) ∗ vₜ ≈ vₛ
      }}.
  Proof.
    iIntros. iApply simul_pairₜ.
    - iApply (simul_bind' [EctxLet (let: () in ⟨&1, &0⟩)] ∅).
      iApply (simul_mono with "[] [$]").
      iIntros (? ?) "(% & % & -> & -> & ?)".
      do 2 (iApply simul_pure_execₜ; first done).
      iApply simul_pair_detₜ. iIntros.
      iApply simul_post. repeat iExists _. eauto.
    - iApply simul_pure_execₜ; first done.
      iEval (asimpl).
      iApply (simul_bind' [EctxLet ⟨&0, ()⟩] ∅).
      iApply (simul_mono with "[] [$]").
      iIntros (? ?) "(% & % & -> & -> & ?)".
      iApply simul_pure_execₜ; first done.
      iApply simul_pair_detₜ. iIntros.
      iApply simul_post. repeat iExists _. eauto.
  Qed.
  Lemma simul_pair_unitₜ2 eₜ eₛ :
    □ (SIM eₜ ≲ eₛ {{ simul_post_val }}) -∗
    SIM ((), eₜ)
      ≲ eₛ
      {{ λ eₜ' eₛ',
          ∃ blkₜ vₜ vₛ,
          ⌜eₜ' = blkₜ⌝ ∗ ⌜eₛ' = vₛ⌝ ∗ blkₜ ↦ₜ (()%V, vₜ) ∗ vₜ ≈ vₛ
      }}.
  Proof.
    iIntros. iApply simul_pairₜ.
    - iApply simul_pure_execₜ; first done.
      iEval (asimpl).
      iApply (simul_bind' [EctxLet ⟨(), &0⟩] ∅).
      iApply (simul_mono with "[] [$]").
      iIntros (? ?) "(% & % & -> & -> & ?)".
      iApply simul_pure_execₜ; first done.
      iApply simul_pair_detₜ. iIntros.
      iApply simul_post. repeat iExists _. eauto.
    - iApply (simul_bind' [EctxLet (let: #() in ⟨&0, &1⟩)] ∅).
      iApply (simul_mono with "[] [$]").
      iIntros (? ?) "(% & % & -> & -> & ?)".
      do 2 (iApply simul_pure_execₜ; first done).
      iApply simul_pair_detₜ. iIntros.
      iApply simul_post. repeat iExists _. eauto.
  Qed.

  Lemma simul_match_block blkₜ eₜ1 eₜ2 blkₛ eₛ1 eₛ2 Φ :
    blkₜ ≈ blkₛ -∗
    ( ∀ vₜ1 vₜ2 vₛ1 vₛ2,
      (vₜ1, vₜ2) ≈ (vₛ1, vₛ2) -∗
      SIM eₜ2.[#vₜ2, #vₜ1/] ≲ eₛ2.[#vₛ2, #vₛ1/] {{ Φ }}
    ) -∗
    SIM match: blkₜ with () => eₜ1 | _ => eₜ2 end
      ≲ match: blkₛ with () => eₛ1 | _ => eₛ2 end
      {{ Φ }}.
  Proof.
    iIntros "#? H". iApply simul_head_step. iIntros. iModIntro.
    iDestruct (simul_heap_bij_valid_block with "[$] [$]") as
      ([vₜ1 vₜ2] [vₛ1 vₛ2]) "#(% & % & ? & ?)".
    unfold_state_eqns.
    iSplit.
    { iPureIntro. repeat eexists. unshelve econstructor; [exact (vₜ1, vₜ2) | | done].
      unfold_state_eqns. done.
    }
    iIntros. invert_head_step. unfold_state_eqns.
    iModIntro. repeat iExists _. iSplit.
    { iPureIntro. repeat eexists. unshelve econstructor; [exact (vₛ1, vₛ2) | | done].
      unfold_state_eqns. done.
    }
    iFrame. iApply "H". iSplit; done.
  Qed.

  Lemma simul_storeₜ blkₜ iₜ vₜ eₛ Φ :
    (blkₜ, iₜ) ↦ₜ- -∗
    ((blkₜ, iₜ) ↦ₜ vₜ -∗ SIM () ≲ eₛ {{ Φ }}) -∗
    SIM blkₜ .# iₜ <- vₜ ≲ eₛ {{ Φ }}.
  Proof.
    iIntros "(% & Hblkₜ) H". iApply simul_head_stepₜ. iIntros. iModIntro. iSplit.
    { iDestruct (simul_heap_validₜ with "[$] [$]") as "%". eauto with tmc_lang. }
    iIntros "* %Hstep". invert Hstep.
    iMod (simul_heap_updateₜ with "[$] [Hblkₜ]") as "(? & ?)"; first by iExists _.
    iModIntro. iFrame. iApply "H". done.
  Qed.
  Lemma simul_storeₛ eₜ blkₛ iₛ vₛ Φ :
    (blkₛ, iₛ) ↦ₛ- -∗
    ((blkₛ, iₛ) ↦ₛ vₛ -∗ SIM eₜ ≲ () {{ Φ }}) -∗
    SIM eₜ ≲ blkₛ .# iₛ <- vₛ {{ Φ }}.
  Proof.
    iIntros "(% & Hblkₛ) H". iApply simul_head_stepₛ. iIntros.
    iDestruct (simul_heap_validₛ with "[$] [$]") as "%".
    iMod (simul_heap_updateₛ with "[$] [Hblkₛ]") as "(? & ?)"; first by iExists _.
    iModIntro. repeat iExists _. iSplit; first (simpl; eauto with tmc_lang).
    iFrame. iApply "H". done.
  Qed.

  Lemma simul_store blkₜ vₜ blkₛ vₛ i Φ :
    (blkₜ, i) ≈ (blkₛ, i) -∗
    vₜ ≈ vₛ -∗
    SIM () ≲ () {{ Φ }} -∗
    SIM blkₜ .# i <- vₜ ≲ blkₛ .# i <- vₛ {{ Φ }}.
  Proof.
    iIntros. iApply simul_head_step. iIntros. iModIntro.
    iDestruct (simul_heap_bij_valid with "[$] [$]") as (vₜ' vₛ') "#(% & % & ?)".
    iSplit; first eauto with tmc_lang.
    iIntros. invert_head_step.
    iMod (simul_heap_bij_update _ _ _ _ vₜ with "[$] [$] [$]"). iModIntro.
    repeat iExists _. iSplit; first eauto with tmc_lang. iFrame.
  Qed.

  Lemma simul_heap_bij_insert blkₜ vₜ eₜ blkₛ vₛ eₛ i Φ :
    ((blkₜ, i) ≈ (blkₛ, i) -∗ SIM eₜ ≲ eₛ {{ Φ }}) -∗
    (blkₜ, i) ⟷ (blkₛ, i) -∗
    SIM eₜ ≲ eₛ {{ Φ }}.
  Proof.
    iIntros "H ?". iApply simul_update_state_interp. iIntros.
    iMod (simul_heap_bij_insert with "[$] [$]") as "(? & ?)".
    iModIntro. iFrame. iApply ("H" with "[$]").
  Qed.
End tmc_simul_heap.
