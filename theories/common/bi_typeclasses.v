From iris.bi Require Import
  bi.
From iris.proofmode Require Import
  proofmode.

From tmc.common Require Import
  prelude.

Class BiEquiv (PROP : bi) X :=
  bi_equiv : X → X → PROP.
Infix "≈" := bi_equiv
( at level 70,
  no associativity
) : bi_scope.
Infix "≈@{ X }" := (@bi_equiv _ X _)
( at level 70,
  no associativity,
  only parsing
) : bi_scope.
Notation "(≈)" := bi_equiv
( only parsing
) : bi_scope.
Notation "(≈@{ X } )" := (@bi_equiv _ X _)
( only parsing
) : bi_scope.
Notation "( x ≈.)" := (bi_equiv x)
( only parsing
) : bi_scope.
Notation "(.≈ x )" := (λ y, bi_equiv y x)
( only parsing
) : bi_scope.

Class BiWellFormed (PROP : bi) X :=
  bi_well_formed : X → X → PROP.

Section Meet.
  Context {PROP : bi}.

  Global Instance bi_pred2_meet X1 X2 : Meet (X1 → X2 → PROP) := (
    λ Φ1 Φ2 x1 x2,
      Φ1 x1 x2 ∧ Φ2 x1 x2
  )%I.

  Global Instance bi_pred3_meet X1 X2 X3 : Meet (X1 → X2 → X3 → PROP) := (
    λ Φ1 Φ2 x1 x2 x3,
      Φ1 x1 x2 x3 ∧ Φ2 x1 x2 x3
  )%I.
End Meet.

Section Join.
  Context {PROP : bi}.

  Global Instance bi_pred2_join X1 X2 : Join (X1 → X2 → PROP) := (
    λ Φ1 Φ2 x1 x2,
      Φ1 x1 x2 ∨ Φ2 x1 x2
  )%I.

  Global Instance bi_pred3_join X1 X2 X3 : Join (X1 → X2 → X3 → PROP) := (
    λ Φ1 Φ2 x1 x2 x3,
      Φ1 x1 x2 x3 ∨ Φ2 x1 x2 x3
  )%I.
End Join.

Class Wand X Y := wand: X → X → Y.
Notation "Φ1 --∗ Φ2" := (wand Φ1 Φ2)%I
( at level 99,
  Φ2 at level 200,
  right associativity,
  format "'[' Φ1  --∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.

Section Wand.
  Context `{BiBUpd PROP}.

  Global Instance bi_pred2_wand X1 X2 : Wand (X1 → X2 → PROP) PROP := (
    λ Φ1 Φ2,
      ∀ x1 x2, Φ1 x1 x2 -∗ Φ2 x1 x2
  )%I.
  Global Instance bi_pred2_wand_ne (X1 X2 : ofe) n
  : Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) $
    @wand (X1 -d> X2 -d> PROP) PROP _.
  Proof.
    rewrite /wand. solve_proper.
  Qed.
  Global Instance bi_pred2_wand_proper (X1 X2 : ofe)
  : Proper ((≡) ==> (≡) ==> (≡)) $
    @wand (X1 -d> X2 -d> PROP) PROP _.
  Proof.
    rewrite /wand. solve_proper.
  Qed.

  Global Instance bi_pred3_wand X1 X2 X3 : Wand (X1 → X2 → X3 → PROP) PROP := (
    λ Φ1 Φ2,
      ∀ x1 x2 x3, Φ1 x1 x2 x3 -∗ Φ2 x1 x2 x3
  )%I.
  Global Instance bi_pred3_wand_ne (X1 X2 X3 : ofe) n
  : Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) $
    @wand (X1 -d> X2 -d> X3 -d> PROP) PROP _.
  Proof.
    rewrite /wand /bi_pred3_wand.
    intros ? ? H1 ? ? H2.
    repeat (f_equiv || apply H1 || apply H2).
  Qed.
  Global Instance bi_pred3_wand_proper (X1 X2 X3 : ofe)
  : Proper ((≡) ==> (≡) ==> (≡)) $
    @wand (X1 -d> X2 -d> X3 -d> PROP) PROP _.
  Proof.
    rewrite /wand /bi_pred3_wand.
    intros ? ? H1 ? ? H2.
    repeat (f_equiv || apply H1 || apply H2).
  Qed.
End Wand.

Section BUpd.
  Context `{BiBUpd PROP}.

  Global Instance bi_pred2_bupd X1 X2 : BUpd (X1 → X2 → PROP) := (
    λ Φ x1 x2,
      |==> Φ x1 x2
  )%I.
  Global Instance bi_pred2_bupd_ne (X1 X2 : ofe) n
  : Proper ((≡{n}≡) ==> (≡{n}≡)) $
    @bupd (X1 -d> X2 -d> PROP) _.
  Proof.
    rewrite /bupd. solve_proper.
  Qed.
  Global Instance bi_pred2_bupd_proper (X1 X2 : ofe)
  : Proper ((≡) ==> (≡)) $
    @bupd (X1 -d> X2 -d> PROP) _.
  Proof.
    rewrite /bupd. solve_proper.
  Qed.
  Lemma bi_pred2_bupd_intro X1 X2 (Φ : X1 → X2 → PROP) :
    ⊢ Φ --∗ |==> Φ.
  Proof.
    by iIntros (? ?) "? !>".
  Qed.

  Global Instance bi_pred3_bupd X1 X2 X3 : BUpd (X1 → X2 → X3 → PROP) := (
    λ Φ x1 x2 x3,
      |==> Φ x1 x2 x3
  )%I.
  Global Instance bi_pred3_bupd_ne (X1 X2 X3 : ofe) n
  : Proper ((≡{n}≡) ==> (≡{n}≡)) $
    @bupd (X1 -d> X2 -d> X3 -d> PROP) _.
  Proof.
    rewrite /bupd /bi_pred3_bupd.
    intros ? ? H1 ? ? H2.
    repeat (f_equiv || apply H1 || apply H2).
  Qed.
  Global Instance bi_pred3_bupd_proper (X1 X2 X3 : ofe)
  : Proper ((≡) ==> (≡)) $
    @bupd (X1 -d> X2 -d> X3 -d> PROP) _.
  Proof.
    rewrite /bupd /bi_pred3_bupd.
    intros ? ? H1 ? ? H2.
    repeat (f_equiv || apply H1 || apply H2).
  Qed.
  Lemma bi_pred3_bupd_intro X1 X2 X3 (Φ : X1 → X2 → X3 → PROP) :
    ⊢ Φ --∗ |==> Φ.
  Proof.
    by iIntros (? ? ?) "? !>".
  Qed.
End BUpd.

Notation "Φ1 ===∗ Φ2" := (Φ1 --∗ |==> Φ2)%I
( at level 99,
  Φ2 at level 200,
  right associativity,
  format "'[' Φ1  ===∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
Notation "(===∗@{ X } )" := (λ Φ1 Φ2 : X, Φ1 ===∗ Φ2)%I
: bi_scope.

Section WandBUpd.
  Context `{BiBUpd PROP}.

  Global Instance bi_pred2_wand_bupd_ne (X1 X2 : ofe) n
  : Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) $
    (===∗@{X1 -d> X2 -d> PROP})%I.
  Proof.
    solve_proper.
  Qed.
  Global Instance bi_pred2_wand_bupd_proper (X1 X2 : ofe)
  : Proper ((≡) ==> (≡) ==> (≡)) $
    (===∗@{X1 -d> X2 -d> PROP})%I.
  Proof.
    solve_proper.
  Qed.
  Lemma bi_pred2_wand_wand_bupd X1 X2 (Φ1 Φ2 : X1 → X2 → PROP) :
    ⊢ (Φ1 --∗ Φ2) -∗ (Φ1 ===∗ Φ2).
  Proof.
    iIntros "H" (? ?) "? !>". by iApply "H".
  Qed.

  Global Instance bi_pred3_wand_bupd_ne (X1 X2 X3 : ofe) n
  : Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) $
    (===∗@{X1 -d> X2 -d> X3 -d> PROP})%I.
  Proof.
    solve_proper.
  Qed.
  Global Instance bi_pred3_wand_bupd_proper (X1 X2 X3 : ofe)
  : Proper ((≡) ==> (≡) ==> (≡)) $
    (===∗@{X1 -d> X2 -d> X3 -d> PROP})%I.
  Proof.
    solve_proper.
  Qed.
  Lemma bi_pred3_wand_wand_bupd X1 X2 X3 (Φ1 Φ2 : X1 → X2 → X3 → PROP) :
    ⊢ (Φ1 --∗ Φ2) -∗ (Φ1 ===∗ Φ2).
  Proof.
    iIntros "H" (? ? ?) "? !>". by iApply "H".
  Qed.
End WandBUpd.
