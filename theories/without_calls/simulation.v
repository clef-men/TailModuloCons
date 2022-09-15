From iris.bi Require Import
  bi
  fixpoint.
From iris.base_logic Require Import
  bi.
From iris.proofmode Require Import
  proofmode.

From tmc.common Require Import
  prelude
  tactics.
From tmc.common Require Export
  bi_typeclasses.
From tmc.without_calls Require Import
  language.lang
  refinement.

Class SimGS (PROP : bi) (Λ : lang) :=
  sim_state_inv : state Λ → state Λ → PROP.

Class Sim (PROP : bi) (Λ : lang) :=
  sim : (expr Λ → expr Λ → PROP) → expr Λ → expr Λ → PROP.
Notation "eₜ '≲' eₛ '{{' Φ } }" := (sim Φ eₜ eₛ)
( at level 70,
  Φ at level 200,
  format "'[hv' eₜ  '/' ≲  '/' eₛ  '/' {{  '[ ' Φ  ']' } } ']'"
) : bi_scope.

Class SimStuck (PROP : bi) (Λ : lang) :=
  simstuck : (expr Λ → expr Λ → PROP) → expr Λ → expr Λ → PROP.
Notation "eₜ '≲' eₛ '[{' Φ } ]" := (simstuck Φ eₜ eₛ)
( at level 70,
  Φ at level 200,
  format "'[hv' eₜ  '/' ≲  '/' eₛ  '/' [{  '[ ' Φ  ']' } ] ']'"
) : bi_scope.

Section sim.
  Context `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context `{!BiPlainly PROP, !BiBUpdPlainly PROP}.
  Context `{SimGS PROP Λ}.
  Notation expr_rel := (exprO Λ -d> exprO Λ -d> PROP).
  Implicit Types e eₜ eₛ : expr Λ.
  Implicit Types σ σₜ σₛ : state Λ.
  Implicit Types Φ : expr_rel.
  Implicit Types Ψ : expr_rel → expr_rel.

  Local Instance expr_rel_func_ne Ψ `{Hne : !NonExpansive Ψ} n
  : Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) Ψ.
  Proof.
    intros
      Φ1 Φ2 HΦ
      eₜ1 eₜ2 ->%discrete_iff%leibniz_equiv
      eₛ1 eₛ2 ->%discrete_iff%leibniz_equiv
    ; [|apply _..].
    eapply Hne, HΦ.
  Qed.

  Definition sim_inner (Ψ : expr_rel -d> expr_rel) : expr_rel -d> expr_rel := (
    λ Φ eₜ eₛ,
      ∀ σₜ σₛ, sim_state_inv σₜ σₛ -∗ |==> (
        sim_state_inv σₜ σₛ ∗ Φ eₜ eₛ
      ) ∨ (
        ∃ eₛ' σₛ', ⌜tc step (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
        sim_state_inv σₜ σₛ' ∗ Ψ Φ eₜ eₛ'
      ) ∨ (
        ⌜reducible eₜ σₜ⌝ ∗ ∀ eₜ' σₜ', ⌜step (eₜ, σₜ) (eₜ', σₜ')⌝ -∗ |==>
        ∃ eₛ' σₛ', ⌜rtc step (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
        sim_state_inv σₜ' σₛ' ∗ Ψ Φ eₜ' eₛ'
      )
  )%I.

  Instance sim_inner_ne n
  : Proper (
      ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
      ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
      (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)
    ) sim_inner.
  Proof.
    intros
      Ψ1 Ψ2 HΨ Φ1 Φ2 HΦ
      eₜ1 eₜ2 Heₜ%discrete_iff%leibniz_equiv
      eₛ1 eₛ2 Heₛ%discrete_iff%leibniz_equiv
    ; [| apply _..].
    subst. rewrite /sim_inner.
    repeat (f_equiv || apply HΦ || eapply HΨ || reflexivity || intros ? ?).
  Qed.
  Instance sim_inner_proper
  : Proper (
      ((≡) ==> (≡) ==> (≡)) ==>
      ((≡) ==> (≡) ==> (≡)) ==>
      (≡) ==> (≡) ==> (≡)
    ) sim_inner.
  Proof.
    intros
      Ψ1 Ψ2 HΨ Φ1 Φ2 HΦ
      eₜ1 eₜ2 Heₜ%leibniz_equiv
      eₛ1 eₛ2 Heₛ%leibniz_equiv.
    subst. rewrite /sim_inner.
    repeat (f_equiv || apply HΦ || eapply HΨ || reflexivity || intros ? ?).
  Qed.

  Lemma sim_inner_mono Ψ1 Ψ2 :
    ⊢ □ (Ψ1 --∗ Ψ2) →
      sim_inner Ψ1 --∗ sim_inner Ψ2.
  Proof.
    iIntros "#Hmono" (? ? ?) " Hsim". rewrite /sim_inner. iIntros "* Hinv".
    iMod ("Hsim" with "Hinv") as "[? | [Hsim | Hsim]]"; iModIntro; first auto.
    - iRight. iLeft.
      iDestruct "Hsim" as (? ?) "(% & ? & ?)".
      repeat iExists _. iFrame. iSplit; first done.
      iApply ("Hmono" with "[$]").
    - iRight. iRight.
      iDestruct "Hsim" as "($ & Hsim)".
      iIntros "* %".
      iMod ("Hsim" with "[% //]") as (? ?) "(% & ? & ?)". iModIntro.
      repeat iExists _. iFrame. iSplit; first done.
      by iApply "Hmono".
  Qed.
  Lemma sim_inner_strong_mono Ψ1 Ψ2 :
    ⊢ □ (∀ Φ1 Φ2, (Φ1 ===∗ Φ2) -∗ Ψ1 Φ1 --∗ Ψ2 Φ2) →
      ∀ Φ1 Φ2, (Φ1 ===∗ Φ2) -∗ sim_inner Ψ1 Φ1 --∗ sim_inner Ψ2 Φ2.
  Proof.
    iIntros "#Hmono * HΦ" (? ?) "Hsim". rewrite /sim_inner. iIntros "* Hinv".
    iMod ("Hsim" with "Hinv") as "[(? & ?) | [Hsim | Hsim]]".
    - iMod ("HΦ" with "[$]"). iModIntro.
      iLeft. iFrame.
    - iModIntro. iRight. iLeft.
      iDestruct "Hsim" as (? ?) "(% & ? & ?)".
      repeat iExists _. iFrame. iSplit; first auto.
      iApply ("Hmono" with "[$] [$]").
    - iModIntro. iRight. iRight.
      iDestruct "Hsim" as "($ & Hsim)".
      iIntros "* %".
      iMod ("Hsim" with "[% //]") as (? ? ?) "(? & ?)". iModIntro.
      repeat iExists _. iFrame. iSplit; first auto.
      iApply ("Hmono" with "[$] [$]").
  Qed.

  Lemma sim_inner_base Ψ Φ :
    ⊢ Φ --∗ sim_inner Ψ Φ.
  Proof.
    iIntros (? ?) "?". iIntros (? ?) "? !>". iLeft. iFrame.
  Qed.

  Definition sim_body (Ψ : prodO (prodO expr_rel (exprO Λ)) (exprO Λ) → PROP)
  : prodO (prodO expr_rel (exprO Λ)) (exprO Λ) → PROP :=
    uncurry3 $ sim_inner $ curry3 Ψ.
  Local Instance : BiMonoPred sim_body.
  Proof.
    constructor.
    - iIntros (Φ1 Φ2 HΦ1 HΦ2) "#HΦ". iIntros ([[Φ eₜ] eₛ]). simpl.
      iApply (sim_inner_mono with "[]"); iModIntro.
      iIntros (? ? ?). iApply "HΦ".
    - intros Ψ HΨ n [[Φ1 eₜ1] eₛ1] [[Φ2 eₜ2] eₛ2] [[HΦ]].
      eapply sim_inner_ne; eauto.
      + intros ? ? ? ? ? ? ?. eapply HΨ. done.
      + intros ? ? ->%leibniz_equiv ? ? ->%leibniz_equiv. eapply HΦ.
  Qed.
  Global Instance : Sim PROP Λ :=
    curry3 $ bi_least_fixpoint sim_body.

  Lemma sim_unfold :
    sim = curry3 $ bi_least_fixpoint sim_body.
  Proof. auto. Qed.
  Lemma sim_fixpoint Φ eₜ eₛ :
    eₜ ≲ eₛ {{ Φ }}%I ≡ sim_inner sim Φ eₜ eₛ.
  Proof.
    rewrite sim_unfold /curry3 least_fixpoint_unfold /uncurry3 //=.
  Qed.

  Lemma sim_strong_ind Ψ :
    NonExpansive Ψ →
    ⊢ □ (sim_inner (Ψ ⊓ sim) --∗ Ψ) -∗
      sim --∗ Ψ.
  Proof.
    iIntros (?) "#Hind". iIntros (Φ eₜ eₛ) "?".
    change (Ψ Φ eₜ eₛ) with (uncurry3 Ψ (Φ, eₜ, eₛ)).
    iApply (least_fixpoint_ind with "[#] [$]").
    iIntros "!>" ([[]]) "**".
    iApply ("Hind" with "[$]").
  Qed.
  Lemma sim_ind Ψ :
    NonExpansive Ψ →
    ⊢ □ (sim_inner Ψ --∗ Ψ) -∗
      sim --∗ Ψ.
  Proof.
    iIntros (?) "#Hind". iIntros (? ? ?) "?".
    iApply sim_strong_ind; last done.
    iIntros "!>" (? ? ?) "?".
    iApply "Hind". iApply sim_inner_mono; last done.
    iIntros "!>" (? ? ?) "H". iEval (cbv) in "H". by iDestruct "H" as "(? & _)".
  Qed.

  Lemma sim_bupd_mono Φ1 Φ2 :
    (Φ1 ===∗ Φ2) -∗
    sim Φ1 --∗ sim Φ2.
  Proof.
    iIntros "**" (eₜ eₛ) "**".
    iApply (sim_strong_ind (
      λ Φ1 eₜ eₛ,
        ∀ Φ2, (Φ1 ===∗ Φ2) -∗ eₜ ≲ eₛ {{ Φ2 }}
    )%I with "[#] [$]"); [solve_proper | | done].
    iIntros "!>". clear eₜ eₛ. iIntros (Φ eₜ eₛ) "Hsim **".
    iEval (rewrite sim_fixpoint).
    iApply (sim_inner_strong_mono with "[#] [$]"); last done.
    iIntros "!> **" (? ?) "Hind".
    by iApply "Hind".
  Qed.
  Lemma sim_mono Φ1 Φ2 :
    (Φ1 --∗ Φ2) -∗
    sim Φ1 --∗ sim Φ2.
  Proof.
    iIntros "HΦ" (? ?) "**".
    iApply (sim_bupd_mono with "[HΦ] [$]").
    by iApply bi_pred2_wand_wand_bupd.
  Qed.

  Lemma sim_base Φ :
    ⊢ Φ --∗ sim Φ.
  Proof.
    iIntros (? ?) "?". iApply sim_fixpoint. by iApply sim_inner_base.
  Qed.

  Lemma sim_bupd Φ :
    ⊢ sim (|==> Φ) --∗ sim Φ.
  Proof.
    iApply sim_bupd_mono. by iIntros (? ?) "?".
  Qed.

  Lemma sim_bind Kₜ `{!LangFrame Kₜ} Kₛ `{!LangFrame Kₛ} Φ eₜ eₛ :
    eₜ ≲ eₛ {{ λ eₜ' eₛ', Kₜ eₜ' ≲ Kₛ eₛ' {{ Φ }} }} -∗
    Kₜ eₜ ≲ Kₛ eₛ {{ Φ }}.
  Proof.
    set Ψ : expr_rel → expr_rel := (
      λ Φ' eₜ' eₛ',
        (∀ eₜ'' eₛ'', Φ' eₜ'' eₛ'' -∗ Kₜ eₜ'' ≲ Kₛ eₛ'' {{ Φ }}) -∗
        Kₜ eₜ' ≲ Kₛ eₛ' {{ Φ }}
    )%I.
    cut (⊢ sim --∗ Ψ).
    { iIntros (HΨ) "**". iApply (HΨ with "[$]"). auto. }
    clear eₜ eₛ. iApply sim_ind; first solve_proper.
    iIntros "!>" (Φ' eₜ' eₛ') "Hsim Hcont".
    iApply sim_fixpoint. iIntros (? ?) "**".
    iMod ("Hsim" with "[$]") as "[Hsim | [Hsim | Hsim]]".
    - iDestruct "Hsim" as "(? & ?)".
      iDestruct (sim_fixpoint with "(Hcont [$])") as "Hsim".
      iMod ("Hsim" with "[$]"). iModIntro. iFrame.
    - iDestruct "Hsim" as (? ?) "(% & ? & Hsim)".
      iModIntro. iRight. iLeft. repeat iExists _. iSplit.
      + iPureIntro. apply lang_frame_tc_step; done.
      + iFrame. iApply "Hsim". iFrame.
    - iDestruct "Hsim" as "(% & Hsim)".
      iModIntro. iRight. iRight. iSplit.
      + iPureIntro. apply lang_frame_reducible; auto.
      + iIntros "*" ([* Hstep]). simplify_eq.
        apply lang_frame_prim_step_inv in Hstep as (? & -> & ?); first last.
        { eauto using reducible_not_val. }
        iMod ("Hsim" with "[%]") as (? ?) "(% & ? & HΨ)".
        { econstructor; eauto. }
        iModIntro. repeat iExists _. iSplit.
        * iPureIntro. apply lang_frame_rtc_step; eauto.
        * iFrame. by iApply "HΨ".
  Qed.
  Lemma sim_decompose Φ1 Φ2 :
    (Φ1 --∗ sim Φ2) -∗
    sim Φ1 --∗ sim Φ2.
  Proof.
    iIntros "HΦ" (eₜ eₛ) "?".
    change eₜ with (id eₜ). change eₛ with (id eₛ).
    iApply sim_bind.
    by iApply (sim_mono with "[HΦ] [$]").
  Qed.

  Lemma bupd_sim :
    ⊢ (|==> sim) --∗ sim.
  Proof.
    iIntros (? ? ?) "Hsim". rewrite sim_fixpoint. iIntros (? ?) "?".
    iMod "Hsim". rewrite sim_fixpoint. by iMod ("Hsim" with "[$]").
  Qed.

  Lemma sim_frame_r R Φ eₜ eₛ :
    eₜ ≲ eₛ {{ Φ }} ∗ R -∗
    eₜ ≲ eₛ {{ λ eₜ' eₛ', Φ eₜ' eₛ' ∗ R }}.
  Proof.
    iIntros "(? & HR)".
    iApply (sim_mono with "[HR] [$]").
    iIntros (? ?) "?". iSplitR "HR"; auto.
  Qed.
  Lemma sim_frame_l R Φ eₜ eₛ :
    R ∗ eₜ ≲ eₛ {{ Φ }} -∗
    eₜ ≲ eₛ {{ λ eₜ' eₛ', R ∗ Φ eₜ' eₛ' }}.
  Proof.
    iIntros "(HR & ?)".
    iApply (sim_mono with "[HR] [$]").
    iIntros (? ?) "?". iSplitL "HR"; auto.
  Qed.

  Definition sim_post_stuck eₜ eₛ : PROP :=
    ⌜strongly_stuck eₜ ∧ strongly_stuck eₛ⌝.
  Global Instance : SimStuck PROP Λ :=
    λ Φ, sim (sim_post_stuck ⊔ Φ).
  Lemma simstuck_unfold :
    simstuck = λ Φ, sim (sim_post_stuck ⊔ Φ).
  Proof.
    auto.
  Qed.

  Lemma sim_simstuck :
    ⊢ sim --∗ simstuck.
  Proof.
    iIntros (? ? ?) "?". iApply (sim_mono with "[] [$]").
    iIntros (? ?) "?". by iRight.
  Qed.

  Lemma simstuck_bupd_mono Φ1 Φ2 :
    (Φ1 ===∗ Φ2) -∗
    simstuck Φ1 --∗ simstuck Φ2.
  Proof.
    iIntros "HΦ" (? ?) "?".
    iApply (sim_bupd_mono with "[HΦ] [$]").
    iIntros (? ?) "[? | ?]".
    - iModIntro. by iLeft.
    - iMod ("HΦ" with "[$]"). iModIntro. by iRight.
  Qed.
  Lemma simstuck_mono Φ1 Φ2 :
    (Φ1 --∗ Φ2) -∗
    simstuck Φ1 --∗ simstuck Φ2.
  Proof.
    iIntros "HΦ" (? ?) "**".
    iApply (simstuck_bupd_mono with "[HΦ] [$]").
    by iApply bi_pred2_wand_wand_bupd.
  Qed.

  Lemma simstuck_base Φ :
    ⊢ Φ --∗ simstuck Φ.
  Proof.
    iIntros (? ?) "?".
    iApply sim_base. by iRight.
  Qed.

  Lemma simstuck_bupd Φ :
    ⊢ simstuck (|==> Φ) --∗ simstuck Φ.
  Proof.
    iApply simstuck_bupd_mono. by iIntros (? ?) "?".
  Qed.

  Lemma simstuck_bind Kₜ `{!LangFrame Kₜ} Kₛ `{!LangFrame Kₛ} Φ eₜ eₛ :
    eₜ ≲ eₛ [{ λ eₜ' eₛ', Kₜ eₜ' ≲ Kₛ eₛ' [{ Φ }] }] -∗
    Kₜ eₜ ≲ Kₛ eₛ [{ Φ }].
  Proof.
    iIntros "**". iApply sim_bind.
    iApply (sim_decompose with "[] [$]").
    iIntros (? ?) "[#(% & %) | ?]"; iApply sim_base; last done.
    iApply sim_base. iLeft. eauto using lang_frame_strongly_stuck.
  Qed.
  Lemma simstuck_decompose Φ1 Φ2 :
    (Φ1 --∗ sim Φ2) -∗
    simstuck Φ1 --∗ simstuck Φ2.
  Proof.
    iIntros "HΦ" (eₜ eₛ) "?".
    change eₜ with (id eₜ). change eₛ with (id eₛ).
    iApply simstuck_bind.
    iApply (simstuck_mono with "[HΦ] [$]").
    iIntros (? ?) "?". iApply sim_simstuck. iApply ("HΦ" with "[$]").
  Qed.

  Lemma bupd_simstuck :
    ⊢ (|==> simstuck) --∗ simstuck.
  Proof.
    iIntros (? ? ?) "?". by iApply bupd_sim.
  Qed.

  Lemma simstuck_frame_r R Φ eₜ eₛ :
    eₜ ≲ eₛ [{ Φ }] ∗ R -∗
    eₜ ≲ eₛ [{ λ eₜ' eₛ', Φ eₜ' eₛ' ∗ R }].
  Proof.
    iIntros "(? & HR)".
    iApply (simstuck_mono with "[HR] [$]").
    iIntros (? ?) "?". iSplitR "HR"; auto.
  Qed.
  Lemma simstuck_frame_l R Φ eₜ eₛ :
    R ∗ eₜ ≲ eₛ [{ Φ }] -∗
    eₜ ≲ eₛ [{ λ eₜ' eₛ', R ∗ Φ eₜ' eₛ' }].
  Proof.
    iIntros "(HR & ?)".
    iApply (simstuck_mono with "[HR] [$]").
    iIntros (? ?) "?". iSplitL "HR"; auto.
  Qed.

  Section adequacy.
    Context `{Equiv (val Λ)}.
    Context `{BiEquiv PROP (val Λ)}.
    Context (val_equiv_adequacy : ∀ vₜ vₛ, vₜ ≈ vₛ -∗ ⌜vₜ ≡ vₛ⌝).

    Definition sim_post_val eₜ eₛ := (
      ∃ vₜ vₛ, ⌜eₜ = of_val vₜ⌝ ∗ ⌜eₛ = of_val vₛ⌝ ∗ vₜ ≈ vₛ
    )%I.

    Lemma sim_converge eₜ σₜ eₜ' σₜ' eₛ σₛ :
      eₜ ≲ eₛ [{ sim_post_val }] -∗
      sim_state_inv σₜ σₛ -∗
      ⌜rtc step (eₜ, σₜ) (eₜ', σₜ')⌝ -∗
      ⌜irreducible eₜ' σₜ'⌝ -∗
      ⌜ ∃ eₛ' σₛ',
        rtc step (eₛ, σₛ) (eₛ', σₛ') ∧
        irreducible eₛ' σₛ' ∧
        behaviour_converge eₜ' ⊑ behaviour_converge eₛ'
      ⌝.
    Proof.
      set Ψ : expr_rel → expr_rel := (
        λ Φ eₜ eₛ,
          ∀ σₜ σₛ eₜ' σₜ',
          (Φ --∗ sim_post_stuck ⊔ sim_post_val) -∗
          sim_state_inv σₜ σₛ -∗
          ⌜rtc step (eₜ, σₜ) (eₜ', σₜ')⌝ -∗
          ⌜irreducible eₜ' σₜ'⌝ -∗
          ⌜ ∃ eₛ' σₛ',
            rtc step (eₛ, σₛ) (eₛ', σₛ') ∧
            irreducible eₛ' σₛ' ∧
            behaviour_converge eₜ' ⊑ behaviour_converge eₛ'
          ⌝
      )%I.
      cut (⊢ sim --∗ Ψ).
      { iIntros (HΨ) "**". iApply (HΨ with "[$] [] [$] [//] [//]").
        by iIntros (? ?) "**".
      }
      clear eₜ σₜ eₜ' σₜ' eₛ σₛ. iApply sim_ind; first solve_proper.
      iIntros "!>" (Φ eₜ eₛ) "Hsim". iIntros (σₜ σₛ eₜ' σₜ') "HΦ ? %Hsteps %".
      iMod ("Hsim" with "[$]") as "[Hsim | [Hsim | Hsim]]".
      - iDestruct "Hsim" as "(_ & ?)".
        iDestruct ("HΦ" with "[$]") as "[Hstuck | Hval]".
        + iDestruct "Hstuck" as "(% & %)".
          iPureIntro. exists eₛ, σₛ. split_and!.
          * apply rtc_refl.
          * eauto using strongly_stuck_irreducible.
          * eapply rtc_step_strongly_stuck in Hsteps; eauto. simplify_eq.
            eapply behaviour_refinement_strongly_stuck; auto.
        + iDestruct "Hval" as "(% & % & % & % & ?)".
          iDestruct (val_equiv_adequacy with "[$]") as "%".
          iPureIntro. exists eₛ, σₛ. split_and!.
          * apply rtc_refl.
          * eauto using val_irreducible, of_to_val_flip.
          * eapply rtc_step_val in Hsteps; eauto. simplify_eq.
            eapply behaviour_refinement_val; eauto.
      - iDestruct "Hsim" as (? ?) "(% & ? & HΨ)".
        iDestruct ("HΨ" with "[$] [$] [//] [//]") as "%". simplify.
        iPureIntro. repeat eexists; eauto. eauto using tc_rtc, tc_rtc_r.
      - iDestruct "Hsim" as "(% & Hsim)".
        inversion Hsteps as [| ? []]; simplify_eq; first firstorder.
        iMod ("Hsim" with "[//]") as (? ? ?) "(? & HΨ)".
        iDestruct ("HΨ" with "[$] [$] [//] [//]") as "%". simplify.
        iPureIntro. repeat eexists; [by etrans | eauto..].
    Qed.
    Lemma sim_diverge eₜ σₜ eₛ σₛ :
      eₜ ≲ eₛ [{ sim_post_val }] -∗
      sim_state_inv σₜ σₛ -∗
      ⌜diverge eₜ σₜ⌝ -∗
      False.
    Proof.
      set Ψ : expr_rel → expr_rel := (
        λ Φ eₜ _,
          ∀ σₜ σₛ,
          (Φ --∗ sim_post_stuck ⊔ sim_post_val) -∗
          sim_state_inv σₜ σₛ -∗
          ⌜diverge eₜ σₜ⌝ -∗
          False
      )%I.
      cut (⊢ sim --∗ Ψ).
      { iIntros (HΨ) "**". iApply (HΨ with "[$] [] [$] [//]").
        by iIntros (? ?) "**".
      }
      clear eₜ σₜ eₛ σₛ. iApply sim_ind; first solve_proper.
      iIntros "!>" (Φ eₜ eₛ) "Hsim". iIntros (? ?) "HΦ ? %Hdiv".
      iMod ("Hsim" with "[$]") as "[Hsim | [Hsim | Hsim]]".
      - iDestruct "Hsim" as "(_ & Hsim)".
        iDestruct ("HΦ" with "[$]") as "[Hstuck | Hval]".
        + iDestruct "Hstuck" as "(% & _)". iPureIntro.
          eapply diverge_not_strongly_stuck; eauto.
        + iDestruct "Hval" as "(% & % & % & _)". iPureIntro.
          eapply diverge_not_val; eauto.
      - iDestruct "Hsim" as (? ?) "(% & ? & Hsim)".
        iApply ("Hsim" with "[$] [$] [//]").
      - iDestruct "Hsim" as "(_ & Hsim)". destruct Hdiv.
        iMod ("Hsim" with "[%]") as (? ?) "(% & ? & HΨ)".
        { econstructor; eauto. }
        iApply ("HΨ" with "[$] [$] [//]").
    Qed.
    Lemma sim_refinement eₜ σₜ eₛ σₛ :
      eₜ ≲ eₛ [{ sim_post_val }] -∗
      sim_state_inv σₜ σₛ -∗
      ⌜ ∀ bₜ, has_behaviour eₜ σₜ bₜ →
        ∃ bₛ, has_behaviour eₛ σₛ bₛ ∧ bₜ ⊑ bₛ
      ⌝.
    Proof.
      iIntros "? ?" (? []).
      - iDestruct (sim_converge with "[$] [$] [//] [//]") as "%". simplify.
        iPureIntro. eexists. split; last eauto.
        econstructor. eauto. auto.
      - iDestruct (sim_diverge with "[$] [$] [//]") as "[]".
    Qed.
  End adequacy.
End sim.

Section adequacy.
  Context {M : ucmra}.
  Let PROP := uPredI M.
  Context `{SimGS PROP Λ}.
  Context `{Equiv (val Λ)}.
  Context `{BiEquiv PROP (val Λ)}.
  Context (val_equiv_adequacy : ∀ vₜ vₛ, vₜ ≈ vₛ -∗ ⌜vₜ ≡ vₛ⌝).
  Implicit Types P : PROP.
  Implicit Types e eₜ eₛ : expr Λ.
  Implicit Types σ σₜ σₛ : state Λ.

  Definition isat P := ∃ x : M, ✓{0} x ∧ uPred_holds P 0 x.

  Lemma isat_intro P :
    (⊢ P) → isat P.
  Proof.
    intros HP. exists ε. split; first by apply ucmra_unit_validN.
    apply HP; first by apply ucmra_unit_validN.
    uPred.unseal. done.
  Qed.

  Lemma isat_elim ϕ :
    isat ⌜ϕ⌝ → ϕ.
  Proof.
    unfold isat. uPred.unseal. intros [x [_ Hφ]]. apply Hφ.
  Qed.

  Lemma sim_adequacy eₜ σₜ eₛ σₛ :
    (⊢@{PROP} eₜ ≲ eₛ [{ sim_post_val }] ∗ sim_state_inv σₜ σₛ) →
    ∀ bₜ, has_behaviour eₜ σₜ bₜ →
    ∃ bₛ, has_behaviour eₛ σₛ bₛ ∧ bₜ ⊑ bₛ.
  Proof.
    intros Hiris. apply isat_elim, isat_intro.
    iDestruct Hiris as "[? ?]". iApply sim_refinement; eauto.
  Qed.
End adequacy.
