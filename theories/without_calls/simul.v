From iris.bi Require Import
  bi
  fixpoint.
From iris.base_logic Require Import
  bi.
From iris.proofmode Require Import
  proofmode.

From simuliris.common Require Import
  prelude
  tactics.
From simuliris.common Require Export
  bi_typeclasses.
From simuliris.without_calls Require Import
  lang.ectx_lang
  refinement.

Class SimulGS (PROP : bi) (Λₜ Λₛ : lang) :=
  simul_state_interp : state Λₜ → state Λₛ → PROP.

Class Simul (PROP : bi) exprₜ exprₛ :=
  simul : (exprₜ → exprₛ → PROP) → exprₜ → exprₛ → PROP.
Local Notation "'SIM' eₜ '≲' eₛ '{{' Φ } }" := (simul Φ eₜ eₛ)
( at level 70,
  eₜ, eₛ, Φ at level 200,
  format "'[hv' 'SIM'  eₜ  ≲  '/   ' eₛ  '/' {{  '[ ' Φ  ']' } } ']'"
) : bi_scope.

Section bi.
  Context `{!BiBUpd PROP, !BiAffine PROP, !BiPureForall PROP}.
  Context `{!BiPlainly PROP, !BiBUpdPlainly PROP}.

  Section lang.
    Context `{SimulGS PROP Λₜ Λₛ}.
    Notation expr_rel := (exprO Λₜ -d> exprO Λₛ -d> PROP).
    Implicit Types eₜ : expr Λₜ.
    Implicit Types eₛ : expr Λₛ.
    Implicit Types σₜ : state Λₜ.
    Implicit Types σₛ : state Λₛ.
    Implicit Types Φ : expr_rel.
    Implicit Types Ψ : expr_rel → expr_rel.

    Local Instance expr_rel_func_ne Ψ `{Hne : !NonExpansive Ψ} n :
      Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) Ψ.
    Proof.
      intros
        Φ1 Φ2 HΦ
        eₜ1 eₜ2 ->%discrete_iff%leibniz_equiv
        eₛ1 eₛ2 ->%discrete_iff%leibniz_equiv
      ; [| apply _..].
      eapply Hne, HΦ.
    Qed.

    Definition simul_inner (Ψ : expr_rel -d> expr_rel) : expr_rel -d> expr_rel := (
      λ Φ eₜ eₛ,
        ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗ (
          simul_state_interp σₜ σₛ ∗ ⌜stuck eₜ σₜ⌝ ∗ ⌜stuck eₛ σₛ⌝
        ) ∨ (
          simul_state_interp σₜ σₛ ∗ Φ eₜ eₛ
        ) ∨ (
          ∃ eₛ' σₛ', ⌜tc step (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
          simul_state_interp σₜ σₛ' ∗ Ψ Φ eₜ eₛ'
        ) ∨ (
          ⌜reducible eₜ σₜ⌝ ∗ ∀ eₜ' σₜ', ⌜prim_step eₜ σₜ eₜ' σₜ'⌝ ==∗
          ∃ eₛ' σₛ', ⌜rtc step (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
          simul_state_interp σₜ' σₛ' ∗ Ψ Φ eₜ' eₛ'
        )
    )%I.

    Instance simul_inner_ne n :
      Proper (
        ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
        ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) ==>
        (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)
      ) simul_inner.
    Proof.
      intros
        Ψ1 Ψ2 HΨ Φ1 Φ2 HΦ
        eₜ1 eₜ2 Heₜ%discrete_iff%leibniz_equiv
        eₛ1 eₛ2 Heₛ%discrete_iff%leibniz_equiv
      ; [| apply _..].
      subst. rewrite /simul_inner.
      repeat (f_equiv || apply HΦ || eapply HΨ || reflexivity || intros ? ?).
    Qed.
    Instance simul_inner_proper :
      Proper (
        ((≡) ==> (≡) ==> (≡)) ==>
        ((≡) ==> (≡) ==> (≡)) ==>
        (≡) ==> (≡) ==> (≡)
      ) simul_inner.
    Proof.
      intros
        Ψ1 Ψ2 HΨ Φ1 Φ2 HΦ
        eₜ1 eₜ2 Heₜ%leibniz_equiv
        eₛ1 eₛ2 Heₛ%leibniz_equiv.
      subst. rewrite /simul_inner.
      repeat (f_equiv || apply HΦ || eapply HΨ || reflexivity || intros ? ?).
    Qed.

    Lemma simul_inner_mono Ψ1 Ψ2 :
      ⊢ □ (Ψ1 --∗ Ψ2) →
        simul_inner Ψ1 --∗ simul_inner Ψ2.
    Proof.
      iIntros "#Hmono" (? ? ?) " Hsimul". rewrite /simul_inner. iIntros "* Hinv".
      iMod ("Hsimul" with "Hinv") as "[? | [? | [Hsimul | Hsimul]]]"; iModIntro.
      - eauto.
      - eauto.
      - do 2 iRight. iLeft.
        iDestruct "Hsimul" as (? ?) "(% & ? & ?)".
        repeat iExists _. iFrame. iSplit; first done.
        iApply ("Hmono" with "[$]").
      - do 3 iRight.
        iDestruct "Hsimul" as "($ & Hsimul)".
        iIntros "* %".
        iMod ("Hsimul" with "[//]") as (? ?) "(% & ? & ?)". iModIntro.
        repeat iExists _. iFrame. iSplit; first done.
        by iApply "Hmono".
    Qed.
    Lemma simul_inner_strong_mono Ψ1 Ψ2 :
      ⊢ □ (∀ Φ1 Φ2, (Φ1 ===∗ Φ2) -∗ Ψ1 Φ1 --∗ Ψ2 Φ2) →
        ∀ Φ1 Φ2, (Φ1 ===∗ Φ2) -∗ simul_inner Ψ1 Φ1 --∗ simul_inner Ψ2 Φ2.
    Proof.
      iIntros "#Hmono * HΦ" (? ?) "Hsimul". rewrite /simul_inner. iIntros "* Hinv".
      iMod ("Hsimul" with "Hinv") as "[Hsimul | [Hsimul | [Hsimul | Hsimul]]]".
      - eauto.
      - iDestruct "Hsimul" as "(? & ?)".
        iMod ("HΦ" with "[$]"). iModIntro.
        iRight. iLeft. iFrame.
      - iModIntro. do 2 iRight. iLeft.
        iDestruct "Hsimul" as (? ?) "(% & ? & ?)".
        repeat iExists _. iFrame. iSplit; first eauto.
        iApply ("Hmono" with "[$] [$]").
      - iModIntro. do 3 iRight.
        iDestruct "Hsimul" as "($ & Hsimul)".
        iIntros "* %".
        iMod ("Hsimul" with "[//]") as (? ? ?) "(? & ?)". iModIntro.
        repeat iExists _. iFrame. iSplit; first eauto.
        iApply ("Hmono" with "[$] [$]").
    Qed.

    Definition simul_body (Ψ : prodO (prodO expr_rel (exprO Λₜ)) (exprO Λₛ) → PROP)
    : prodO (prodO expr_rel (exprO Λₜ)) (exprO Λₛ) → PROP :=
      uncurry3 $ simul_inner $ curry3 Ψ.
    Local Instance :
      BiMonoPred simul_body.
    Proof.
      constructor.
      - iIntros (Φ1 Φ2 HΦ1 HΦ2) "#HΦ". iIntros ([[Φ eₜ] eₛ]). simpl.
        iApply (simul_inner_mono with "[]"); iModIntro.
        iIntros (? ? ?). iApply "HΦ".
      - intros Ψ HΨ n [[Φ1 eₜ1] eₛ1] [[Φ2 eₜ2] eₛ2] [[HΦ]].
        eapply simul_inner_ne; eauto.
        + intros ? ? ? ? ? ? ?. eapply HΨ. done.
        + intros ? ? ->%leibniz_equiv ? ? ->%leibniz_equiv. eapply HΦ.
    Qed.
    Global Instance simul_bi_simul : Simul PROP (expr Λₜ) (expr Λₛ) :=
      curry3 $ bi_least_fixpoint simul_body.

    Lemma simul_eq :
      simul = curry3 $ bi_least_fixpoint simul_body.
    Proof.
      done.
    Qed.
    Lemma simul_fixpoint eₜ eₛ Φ :
      SIM eₜ ≲ eₛ {{ Φ }}%I ≡ simul_inner simul Φ eₜ eₛ.
    Proof.
      rewrite simul_eq /curry3 least_fixpoint_unfold /uncurry3 //=.
    Qed.
    Lemma simul_unfold eₜ eₛ Φ :
      SIM eₜ ≲ eₛ {{ Φ }}%I ≡
      ( ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗ (
          simul_state_interp σₜ σₛ ∗ ⌜stuck eₜ σₜ⌝ ∗ ⌜stuck eₛ σₛ⌝
        ) ∨ (
          simul_state_interp σₜ σₛ ∗ Φ eₜ eₛ
        ) ∨ (
          ∃ eₛ' σₛ', ⌜tc step (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
          simul_state_interp σₜ σₛ' ∗ SIM eₜ ≲ eₛ' {{ Φ }}
        ) ∨ (
          ⌜reducible eₜ σₜ⌝ ∗ ∀ eₜ' σₜ', ⌜prim_step eₜ σₜ eₜ' σₜ'⌝ ==∗
          ∃ eₛ' σₛ', ⌜rtc step (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
          simul_state_interp σₜ' σₛ' ∗ SIM eₜ' ≲ eₛ' {{ Φ }}
        )
      )%I.
    Proof.
      by rewrite simul_fixpoint.
    Qed.

    Lemma simul_strong_ind Ψ :
      NonExpansive Ψ →
      ⊢ □ (simul_inner (Ψ ⊓ simul) --∗ Ψ) -∗
        simul --∗ Ψ.
    Proof.
      iIntros (?) "#Hind". iIntros (Φ eₜ eₛ) "?".
      change (Ψ Φ eₜ eₛ) with (uncurry3 Ψ (Φ, eₜ, eₛ)).
      iApply (least_fixpoint_ind with "[#] [$]").
      iIntros "!>" ([[]]) "**".
      iApply ("Hind" with "[$]").
    Qed.
    Lemma simul_ind Ψ :
      NonExpansive Ψ →
      ⊢ □ (simul_inner Ψ --∗ Ψ) -∗
        simul --∗ Ψ.
    Proof.
      iIntros (?) "#Hind". iIntros (? ? ?) "?".
      iApply simul_strong_ind; last done.
      iIntros "!>" (? ? ?) "?".
      iApply "Hind". iApply simul_inner_mono; last done.
      iIntros "!>" (? ? ?) "H". iEval (cbv) in "H". by iDestruct "H" as "(? & _)".
    Qed.

    Lemma simul_bupd_mono Φ1 Φ2 :
      (Φ1 ===∗ Φ2) -∗
      simul Φ1 --∗ simul Φ2.
    Proof.
      iIntros "**" (eₜ eₛ) "**".
      iApply (simul_strong_ind (
        λ Φ1 eₜ eₛ,
          ∀ Φ2, (Φ1 ===∗ Φ2) -∗ SIM eₜ ≲ eₛ {{ Φ2 }}
      )%I with "[#] [$]"); [solve_proper | | done].
      iIntros "!>". clear eₜ eₛ. iIntros (Φ eₜ eₛ) "Hsimul **".
      iEval (rewrite simul_fixpoint).
      iApply (simul_inner_strong_mono with "[#] [$]"); last done.
      iIntros "!> **" (? ?) "Hind".
      by iApply "Hind".
    Qed.
    Lemma simul_mono Φ1 Φ2 :
      (Φ1 --∗ Φ2) -∗
      simul Φ1 --∗ simul Φ2.
    Proof.
      iIntros "HΦ" (? ?) "**".
      iApply (simul_bupd_mono with "[HΦ] [$]").
      by iApply bi_pred2_wand_wand_bupd.
    Qed.

    Lemma simul_bupd Φ :
      ⊢ simul (|==> Φ) --∗ simul Φ.
    Proof.
      iApply simul_bupd_mono. by iIntros (? ?) "?".
    Qed.
    Lemma bupd_simul :
      ⊢ (|==> simul) --∗ simul.
    Proof.
      iIntros (? ? ?) "Hsimul". iApply simul_unfold. iIntros.
      iMod "Hsimul". rewrite simul_fixpoint. by iMod ("Hsimul" with "[$]").
    Qed.

    Lemma simul_frame_r R eₜ eₛ Φ :
      SIM eₜ ≲ eₛ {{ Φ }} ∗ R -∗
      SIM eₜ ≲ eₛ {{ λ eₜ' eₛ', Φ eₜ' eₛ' ∗ R }}.
    Proof.
      iIntros "(? & HR)".
      iApply (simul_mono with "[HR] [$]").
      iIntros (? ?) "?". iSplitR "HR"; eauto.
    Qed.
    Lemma simul_frame_l R eₜ eₛ Φ :
      R ∗ SIM eₜ ≲ eₛ {{ Φ }} -∗
      SIM eₜ ≲ eₛ {{ λ eₜ' eₛ', R ∗ Φ eₜ' eₛ' }}.
    Proof.
      iIntros "(HR & ?)".
      iApply (simul_mono with "[HR] [$]").
      iIntros (? ?) "?". iSplitL "HR"; eauto.
    Qed.

    Lemma simul_update_state_interp eₜ eₛ Φ :
      ( ∀ σₜ σₛ,
        simul_state_interp σₜ σₛ ==∗
        simul_state_interp σₜ σₛ ∗ SIM eₜ ≲ eₛ {{ Φ }}
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_unfold. iIntros.
      iMod ("H" with "[$]") as "(? & H)".
      iEval (rewrite simul_unfold) in "H". iApply ("H" with "[$]").
    Qed.

    Lemma simul_stuck eₜ eₛ Φ :
      ( ∀ σₜ σₛ,
        simul_state_interp σₜ σₛ -∗
        simul_state_interp σₜ σₛ ∗ ⌜stuck eₜ σₜ ∧ stuck eₛ σₛ⌝
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_unfold. iIntros. iLeft. iModIntro.
      iDestruct ("H" with "[$]") as "(? & % & %)". eauto.
    Qed.
    Lemma simul_strongly_stuck eₜ eₛ Φ :
      StronglyStuck eₜ →
      StronglyStuck eₛ →
      ⊢ SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros. iApply simul_stuck. iIntros. iFrame.
      eauto using strongly_stuck_stuck.
    Qed.

    Lemma simul_post Φ :
      ⊢ Φ --∗ simul Φ.
    Proof.
      iIntros (? ?) "?". iApply simul_unfold. iIntros. iModIntro.
      iRight. iLeft. iFrame.
    Qed.

    Lemma simul_bind Kₜ `{!LangFrame Kₜ} Kₛ `{!LangFrame Kₛ} eₜ eₛ Φ :
      SIM eₜ ≲ eₛ {{ λ eₜ' eₛ', SIM Kₜ eₜ' ≲ Kₛ eₛ' {{ Φ }} }} -∗
      SIM Kₜ eₜ ≲ Kₛ eₛ {{ Φ }}.
    Proof.
      set Ψ : expr_rel → expr_rel := (
        λ Φ' eₜ' eₛ',
          (∀ eₜ'' eₛ'', Φ' eₜ'' eₛ'' -∗ SIM Kₜ eₜ'' ≲ Kₛ eₛ'' {{ Φ }}) -∗
          SIM Kₜ eₜ' ≲ Kₛ eₛ' {{ Φ }}
      )%I.
      cut (⊢ simul --∗ Ψ).
      { iIntros (HΨ) "**". iApply (HΨ with "[$]"). eauto. }
      clear eₜ eₛ. iApply simul_ind; first solve_proper.
      iIntros "!>" (Φ' eₜ' eₛ') "Hsimul Hcont".
      iApply simul_unfold. iIntros "**".
      iMod ("Hsimul" with "[$]") as "[Hsimul | [Hsimul | [Hsimul | Hsimul]]]".
      - iDestruct "Hsimul" as "(? & % & %)".
        iModIntro. iLeft. iFrame. iSplit; iPureIntro; eauto using lang_frame_stuck.
      - iDestruct "Hsimul" as "(? & ?)".
        iDestruct (simul_fixpoint with "(Hcont [$])") as "Hsimul".
        iMod ("Hsimul" with "[$]"). iModIntro. iFrame.
      - iDestruct "Hsimul" as (? ?) "(% & ? & Hsimul)".
        iModIntro. do 2 iRight. iLeft. repeat iExists _. iSplit.
        + iPureIntro. apply lang_frame_tc_step; done.
        + iFrame. iApply "Hsimul". iFrame.
      - iDestruct "Hsimul" as "(% & Hsimul)".
        iModIntro. do 3 iRight. iSplit.
        + iPureIntro. eapply lang_frame_reducible; eauto.
        + iIntros "* %Hstep".
          apply lang_frame_prim_step_inv in Hstep as (? & -> & ?); first last.
          { eauto using reducible_not_val. }
          iMod ("Hsimul" with "[%]") as (? ?) "(% & ? & HΨ)"; first done.
          iModIntro. repeat iExists _. iSplit.
          * iPureIntro. apply lang_frame_rtc_step; eauto.
          * iFrame. by iApply "HΨ".
    Qed.
    Lemma simul_decompose Φ1 Φ2 :
      (Φ1 --∗ simul Φ2) -∗
      simul Φ1 --∗ simul Φ2.
    Proof.
      iIntros "HΦ" (eₜ eₛ) "?".
      iEval (change eₜ with (id eₜ); change eₛ with (id eₛ)).
      iApply simul_bind. iApply (simul_mono with "[HΦ //] [$]").
    Qed.

    Lemma simul_steps eₜ eₛ Φ :
      ( ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗
        ⌜reducible eₜ σₜ⌝ ∗ ∀ eₜ' σₜ', ⌜prim_step eₜ σₜ eₜ' σₜ'⌝ ==∗
        ∃ eₛ' σₛ', ⌜rtc step (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
        simul_state_interp σₜ' σₛ' ∗ SIM eₜ' ≲ eₛ' {{ Φ }}
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_unfold. iIntros.
      iMod ("H" with "[$]") as "(% & H)". iModIntro.
      do 3 iRight. iSplit; first done. iIntros.
      iMod ("H" with "[//]") as (? ?) "(% & ? & ?)". iModIntro.
      repeat iExists _. iFrame. done.
    Qed.
    Lemma simul_step eₜ eₛ Φ :
      ( ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗
        ⌜reducible eₜ σₜ⌝ ∗ ∀ eₜ' σₜ', ⌜prim_step eₜ σₜ eₜ' σₜ'⌝ ==∗
        ∃ eₛ' σₛ', ⌜prim_step eₛ σₛ eₛ' σₛ'⌝ ∗
        simul_state_interp σₜ' σₛ' ∗ SIM eₜ' ≲ eₛ' {{ Φ }}
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_steps.
      iIntros. iMod ("H" with "[$]") as "($ & H)". iModIntro.
      iIntros. iMod ("H" with "[//]") as (? ?) "(% & ? & ?)". iModIntro.
      repeat iExists _. iFrame. eauto using rtc_once, prim_step_step.
    Qed.

    Lemma simul_stepₜ eₜ eₛ Φ :
      ( ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗
        ⌜reducible eₜ σₜ⌝ ∗ ∀ eₜ' σₜ', ⌜prim_step eₜ σₜ eₜ' σₜ'⌝ ==∗
        simul_state_interp σₜ' σₛ ∗ SIM eₜ' ≲ eₛ {{ Φ }}
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_steps. iIntros.
      iMod ("H" with "[$]") as "(% & H)". iModIntro.
      iSplit; first done. iIntros.
      iMod ("H" with "[//]") as "(? & ?)". iModIntro.
      repeat iExists _. iFrame. done.
    Qed.
    Lemma simul_stepsₛ eₜ eₛ Φ :
      ( ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗
        ∃ eₛ' σₛ', ⌜rtc step (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
        simul_state_interp σₜ σₛ' ∗ SIM eₜ ≲ eₛ' {{ Φ }}
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_unfold. iIntros.
      iMod ("H" with "[$]") as (? ? []%rtc_tc) "(? & Hsim)".
      - simplify. iEval (rewrite simul_unfold) in "Hsim".
        iMod ("Hsim" with "[$]"). iModIntro. done.
      - iModIntro. do 2 iRight. iLeft. repeat iExists _. iFrame. done.
    Qed.
    Lemma simul_stepₛ eₜ eₛ Φ :
      ( ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗
        ∃ eₛ' σₛ', ⌜prim_step eₛ σₛ eₛ' σₛ'⌝ ∗
        simul_state_interp σₜ σₛ' ∗ SIM eₜ ≲ eₛ' {{ Φ }}
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_stepsₛ. iIntros.
      iMod ("H" with "[$]") as (? ?) "(% & ? & ?)". iModIntro.
      repeat iExists _. iFrame. eauto using rtc_once, prim_step_step.
    Qed.

    Lemma simul_pure_stepₜ eₜ1 eₜ2 eₛ Φ :
      pure_step eₜ1 eₜ2 →
      SIM eₜ2 ≲ eₛ {{ Φ }} -∗
      SIM eₜ1 ≲ eₛ {{ Φ }}.
    Proof.
      iIntros ([]) "**". iApply simul_stepₜ. iIntros. iModIntro.
      iSplit; first done. iIntros "*" (?%pure_step_det) "!>". simplify. iFrame.
    Qed.
    Lemma simul_pure_execₜ ϕ n eₜ1 eₜ2 eₛ Φ :
      PureExec ϕ n eₜ1 eₜ2 →
      ϕ →
      SIM eₜ2 ≲ eₛ {{ Φ }} -∗
      SIM eₜ1 ≲ eₛ {{ Φ }}.
    Proof.
      intros * HPureExec Hsteps%pure_exec.
      generalize eₜ1 Hsteps. clear HPureExec Hsteps.
      induction n; intros * Hsteps; invert Hsteps; first done.
      iIntros. iApply simul_pure_stepₜ; first done. iApply IHn; eauto.
    Qed.

    Lemma simul_pure_execₛ ϕ n eₜ eₛ1 eₛ2 Φ :
      PureExec ϕ n eₛ1 eₛ2 →
      ϕ →
      SIM eₜ ≲ eₛ2 {{ Φ }} -∗
      SIM eₜ ≲ eₛ1 {{ Φ }}.
    Proof.
      iIntros (? ?%pure_exec%rtc_nsteps_2) "**".
      iApply simul_stepsₛ. iIntros. iModIntro.
      repeat iExists _. iFrame. iPureIntro.
      eapply rtc_congruence with (f := (., _)); last done.
      eauto using prim_step_step, pure_step_prim_step.
    Qed.
    Lemma simul_pure_stepₛ eₜ eₛ1 eₛ2 Φ :
      pure_step eₛ1 eₛ2 →
      SIM eₜ ≲ eₛ2 {{ Φ }} -∗
      SIM eₜ ≲ eₛ1 {{ Φ }}.
    Proof.
      iIntros. iApply simul_pure_execₛ; eauto using pure_step_pure_exec.
    Qed.

    Section adequacy.
      Context `{Similar (val Λₜ) (val Λₛ)}.
      Context `{BiSimilar PROP (val Λₜ) (val Λₛ)}.
      Context (val_equiv_adequacy : ∀ vₜ vₛ, vₜ ≈ vₛ -∗ ⌜vₜ ≈ vₛ⌝).

      Definition simul_post_val eₜ eₛ := (
        ∃ vₜ vₛ, ⌜eₜ = of_val vₜ⌝ ∗ ⌜eₛ = of_val vₛ⌝ ∗ vₜ ≈ vₛ
      )%I.

      Lemma simul_converges eₜ σₜ eₜ' σₜ' eₛ σₛ :
        SIM eₜ ≲ eₛ {{ simul_post_val }} -∗
        simul_state_interp σₜ σₛ -∗
        ⌜converges eₜ σₜ eₜ' σₜ'⌝ -∗
        ⌜ ∃ eₛ' σₛ',
          converges eₛ σₛ eₛ' σₛ' ∧
          behaviour_converges eₜ' ⊴ behaviour_converges eₛ'
        ⌝.
      Proof.
        set Ψ : expr_rel → expr_rel := (
          λ Φ eₜ eₛ,
            ∀ σₜ σₛ eₜ' σₜ',
            (Φ --∗ simul_post_val) -∗
            simul_state_interp σₜ σₛ -∗
            ⌜converges eₜ σₜ eₜ' σₜ'⌝ -∗
            ⌜ ∃ eₛ' σₛ',
              converges eₛ σₛ eₛ' σₛ' ∧
              behaviour_converges eₜ' ⊴ behaviour_converges eₛ'
            ⌝
        )%I.
        cut (⊢ simul --∗ Ψ).
        { iIntros (HΨ) "**". iApply (HΨ with "[$] [] [$] [//]").
          by iIntros (? ?) "**".
        }
        clear eₜ σₜ eₜ' σₜ' eₛ σₛ. iApply simul_ind; first solve_proper.
        iIntros "!>" (Φ eₜ eₛ) "Hsimul". iIntros (σₜ σₛ eₜ' σₜ') "HΦ ? (%Hsteps & %)".
        iMod ("Hsimul" with "[$]") as "[Hsimul | [Hsimul | [Hsimul | Hsimul]]]".
        - iDestruct "Hsimul" as "(? & % & %)".
          iPureIntro. repeat eexists.
          + eauto using rtc_refl.
          + eauto using stuck_irreducible.
          + eapply rtc_step_stuck in Hsteps; last done. simplify.
            eapply behaviour_refinement_stuck; eauto using stuck_not_val.
        - iDestruct "Hsimul" as "(_ & ?)".
          iDestruct ("HΦ" with "[$]") as "(% & % & % & % & ?)".
          iDestruct (val_equiv_adequacy with "[$]") as "%".
          iPureIntro. exists eₛ, σₛ. split; first split.
          * eauto using rtc_refl.
          * eauto using val_irreducible.
          * eapply rtc_step_val in Hsteps; last done. simplify.
            eapply behaviour_refinement_val; eauto.
        - iDestruct "Hsimul" as (? ?) "(% & ? & HΨ)".
          iDestruct ("HΨ" with "[$] [$] [//]") as "%Hconv".
          rewrite /converges in Hconv. simplify.
          iPureIntro. repeat eexists; eauto. eauto using tc_rtc, tc_rtc_r.
        - iDestruct "Hsimul" as "(% & Hsimul)".
          inversion Hsteps as [| ? []]; simplify; first firstorder.
          iMod ("Hsimul" with "[%]") as (? ? ?) "(? & HΨ)".
          { eauto using step_prim_step. }
          iDestruct ("HΨ" with "[$] [$] [//]") as "%Hconv".
          rewrite /converges in Hconv. simplify.
          iPureIntro. repeat eexists; [by etrans | eauto..].
      Qed.
      Lemma simul_diverges eₜ σₜ eₛ σₛ :
        SIM eₜ ≲ eₛ {{ simul_post_val }} -∗
        simul_state_interp σₜ σₛ -∗
        ⌜diverges eₜ σₜ⌝ -∗
        False.
      Proof.
        set Ψ : expr_rel → expr_rel := (
          λ Φ eₜ _,
            ∀ σₜ σₛ,
            (Φ --∗ simul_post_val) -∗
            simul_state_interp σₜ σₛ -∗
            ⌜diverges eₜ σₜ⌝ -∗
            False
        )%I.
        cut (⊢ simul --∗ Ψ).
        { iIntros (HΨ) "**". iApply (HΨ with "[$] [] [$] [//]").
          by iIntros (? ?) "**".
        }
        clear eₜ σₜ eₛ σₛ. iApply simul_ind; first solve_proper.
        iIntros "!>" (Φ eₜ eₛ) "Hsimul". iIntros (? ?) "HΦ ? %Hdiv".
        iMod ("Hsimul" with "[$]") as "[Hsimul | [Hsimul | [Hsimul | Hsimul]]]".
        - iDestruct "Hsimul" as "(? & % & %)".
          iPureIntro. eapply diverges_not_stuck; eauto.
        - iDestruct "Hsimul" as "(_ & Hsimul)".
          iDestruct ("HΦ" with "[$]") as "(% & % & % & _)".
          iPureIntro. eapply diverges_not_val; eauto.
        - iDestruct "Hsimul" as (? ?) "(% & ? & Hsimul)".
          iApply ("Hsimul" with "[$] [$] [//]").
        - iDestruct "Hsimul" as "(_ & Hsimul)". destruct Hdiv.
          iMod ("Hsimul" with "[%]") as (? ?) "(% & ? & HΨ)"; first done.
          iApply ("HΨ" with "[$] [$] [//]").
      Qed.
      Lemma simul_refinement eₜ σₜ eₛ σₛ :
        SIM eₜ ≲ eₛ {{ simul_post_val }} -∗
        simul_state_interp σₜ σₛ -∗
        ⌜(eₜ, σₜ) ⊴ (eₛ, σₛ)⌝.
      Proof.
        iIntros "? ?" (? []).
        - iDestruct (simul_converges with "[$] [$] [//]") as "%". simplify.
          iPureIntro. eexists. split; last eauto. econstructor. eauto.
        - iDestruct (simul_diverges with "[$] [$] [//]") as "[]".
      Qed.
    End adequacy.
  End lang.

  Section ectx_lang.
    Context {Λₜ : ectx_lang} {Λₛ : ectx_lang}.
    Context `{SimulGS PROP Λₜ Λₛ}.
    Implicit Types eₜ : expr Λₜ.
    Implicit Types eₛ : expr Λₛ.
    Implicit Types σₜ : state Λₜ.
    Implicit Types σₛ : state Λₛ.
    Implicit Types Kₜ : ectx Λₜ.
    Implicit Types Kₛ : ectx Λₛ.

    Lemma simul_bind' Kₜ Kₛ eₜ eₛ Φ :
      SIM eₜ ≲ eₛ {{ λ eₜ' eₛ', SIM Kₜ @@ eₜ' ≲ Kₛ @@ eₛ' {{ Φ }} }} -∗
      SIM Kₜ @@ eₜ ≲ Kₛ @@ eₛ {{ Φ }}.
    Proof.
      rewrite simul_bind //.
    Qed.

    Lemma simul_head_step eₜ eₛ Φ :
      ( ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗
        ⌜head_reducible eₜ σₜ⌝ ∗ ∀ eₜ' σₜ', ⌜head_step eₜ σₜ eₜ' σₜ'⌝ ==∗
        ∃ eₛ' σₛ', ⌜head_step eₛ σₛ eₛ' σₛ'⌝ ∗
        simul_state_interp σₜ' σₛ' ∗ SIM eₜ' ≲ eₛ' {{ Φ }}
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_step.
      iIntros. iMod ("H" with "[$]") as "(% & H)". iModIntro.
      iSplit; first eauto using head_reducible_reducible.
      iIntros "*" (?%head_reducible_prim_step); last done.
      iMod ("H" with "[//]") as (? ?) "(% & ? & ?)". iModIntro.
      repeat iExists _. iSplit; last iFrame.
      naive_solver eauto using head_step_prim_step.
    Qed.

    Lemma simul_head_stepₜ eₜ eₛ Φ :
      ( ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗
        ⌜head_reducible eₜ σₜ⌝ ∗ ∀ eₜ' σₜ', ⌜head_step eₜ σₜ eₜ' σₜ'⌝ ==∗
        simul_state_interp σₜ' σₛ ∗ SIM eₜ' ≲ eₛ {{ Φ }}
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_stepₜ. iIntros.
      iMod ("H" with "[$]") as "(% & H)". iModIntro.
      iSplit; first eauto using head_reducible_reducible.
      iIntros "*" (?%head_reducible_prim_step); last done.
      iMod ("H" with "[//]") as "(? & ?)". iModIntro. iFrame.
    Qed.
    Lemma simul_head_stepₛ eₜ eₛ Φ :
      ( ∀ σₜ σₛ, simul_state_interp σₜ σₛ ==∗
        ∃ eₛ' σₛ', ⌜head_step eₛ σₛ eₛ' σₛ'⌝ ∗
        simul_state_interp σₜ σₛ' ∗ SIM eₜ ≲ eₛ' {{ Φ }}
      ) -∗
      SIM eₜ ≲ eₛ {{ Φ }}.
    Proof.
      iIntros "H". iApply simul_stepₛ. iIntros.
      iMod ("H" with "[$]") as (? ?) "(% & ? & ?)". iModIntro.
      repeat iExists _. iFrame. iPureIntro. by eapply head_step_prim_step.
    Qed.

    Lemma simul_pure_head_stepₜ eₜ1 eₜ2 eₛ Φ :
      pure_head_step eₜ1 eₜ2 →
      SIM eₜ2 ≲ eₛ {{ Φ }} -∗
      SIM eₜ1 ≲ eₛ {{ Φ }}.
    Proof.
      iIntros. iApply simul_pure_stepₜ; eauto using pure_head_step_pure_step.
    Qed.
    Lemma simul_pure_head_execₜ ϕ n eₜ1 eₜ2 eₛ Φ :
      PureHeadExec ϕ n eₜ1 eₜ2 →
      ϕ →
      SIM eₜ2 ≲ eₛ {{ Φ }} -∗
      SIM eₜ1 ≲ eₛ {{ Φ }}.
    Proof.
      iIntros. iApply simul_pure_execₜ; eauto using pure_head_exec_pure_exec.
    Qed.

    Lemma simul_pure_head_stepₛ eₜ eₛ1 eₛ2 Φ :
      pure_head_step eₛ1 eₛ2 →
      SIM eₜ ≲ eₛ2 {{ Φ }} -∗
      SIM eₜ ≲ eₛ1 {{ Φ }}.
    Proof.
      iIntros. iApply simul_pure_stepₛ; eauto using pure_head_step_pure_step.
    Qed.
    Lemma simul_pure_head_execₛ ϕ n eₜ eₛ1 eₛ2 Φ :
      PureHeadExec ϕ n eₛ1 eₛ2 →
      ϕ →
      SIM eₜ ≲ eₛ2 {{ Φ }} -∗
      SIM eₜ ≲ eₛ1 {{ Φ }}.
    Proof.
      iIntros. iApply simul_pure_execₛ; eauto using pure_head_exec_pure_exec.
    Qed.
  End ectx_lang.
End bi.

From iris.base_logic.lib Require Import
  iprop.

Section adequacy.
  Context {Σ : gFunctors}.
  Let PROP := iPropI Σ.
  Context `{SimulGS PROP Λₜ Λₛ}.
  Context `{Similar (val Λₜ) (val Λₛ)}.
  Context `{BiSimilar PROP (val Λₜ) (val Λₛ)}.
  Context (val_equiv_adequacy : ∀ vₜ vₛ, vₜ ≈ vₛ -∗ ⌜vₜ ≈ vₛ⌝).
  Implicit Types P : PROP.
  Implicit Types eₜ : expr Λₜ.
  Implicit Types eₛ : expr Λₛ.
  Implicit Types σₜ : state Λₜ.
  Implicit Types σₛ : state Λₛ.

  Definition sat P :=
    ∃ x, ✓{0} x ∧ uPred_holds P 0 x.

  Lemma sat_intro P :
    (⊢ P) → sat P.
  Proof.
    intros HP. exists ε. split; first by apply ucmra_unit_validN.
    apply HP; first by apply ucmra_unit_validN.
    uPred.unseal. done.
  Qed.

  Lemma sat_elim ϕ :
    sat ⌜ϕ⌝ → ϕ.
  Proof.
    rewrite /sat. uPred.unseal. intros (x & _ & Hϕ). apply Hϕ.
  Qed.

  Lemma simul_adequacy eₜ σₜ eₛ σₛ :
    (⊢@{PROP} SIM eₜ ≲ eₛ {{ simul_post_val }} ∗ simul_state_interp σₜ σₛ) →
    (eₜ, σₜ) ⊴ (eₛ, σₛ).
  Proof.
    intros Hiris. apply sat_elim, sat_intro.
    iDestruct Hiris as "(? & ?)". iApply simul_refinement; eauto.
  Qed.
End adequacy.
