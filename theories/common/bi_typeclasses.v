From iris.bi Require Export
  bi.
From iris.algebra Require Export
  dfrac.
From iris.proofmode Require Import
  proofmode.

From simuliris.common Require Import
  prelude.

Implicit Types PROP : bi.

Section Meet.
  Context {PROP}.

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
  Context {PROP}.

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
  Global Instance bi_pred2_wand_ne (X1 X2 : ofe) n :
    Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) $
    @wand (X1 -d> X2 -d> PROP) PROP _.
  Proof.
    rewrite /wand. solve_proper.
  Qed.
  Global Instance bi_pred2_wand_proper (X1 X2 : ofe) :
    Proper ((≡) ==> (≡) ==> (≡)) $
    @wand (X1 -d> X2 -d> PROP) PROP _.
  Proof.
    rewrite /wand. solve_proper.
  Qed.

  Global Instance bi_pred3_wand X1 X2 X3 : Wand (X1 → X2 → X3 → PROP) PROP := (
    λ Φ1 Φ2,
      ∀ x1 x2 x3, Φ1 x1 x2 x3 -∗ Φ2 x1 x2 x3
  )%I.
  Global Instance bi_pred3_wand_ne (X1 X2 X3 : ofe) n :
    Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) $
    @wand (X1 -d> X2 -d> X3 -d> PROP) PROP _.
  Proof.
    rewrite /wand /bi_pred3_wand.
    intros ? ? H1 ? ? H2.
    repeat (f_equiv || apply H1 || apply H2).
  Qed.
  Global Instance bi_pred3_wand_proper (X1 X2 X3 : ofe) :
    Proper ((≡) ==> (≡) ==> (≡)) $
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
  Global Instance bi_pred2_bupd_ne (X1 X2 : ofe) n :
    Proper ((≡{n}≡) ==> (≡{n}≡)) $
    @bupd (X1 -d> X2 -d> PROP) _.
  Proof.
    rewrite /bupd. solve_proper.
  Qed.
  Global Instance bi_pred2_bupd_proper (X1 X2 : ofe) :
    Proper ((≡) ==> (≡)) $
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
  Global Instance bi_pred3_bupd_ne (X1 X2 X3 : ofe) n :
    Proper ((≡{n}≡) ==> (≡{n}≡)) $
    @bupd (X1 -d> X2 -d> X3 -d> PROP) _.
  Proof.
    rewrite /bupd /bi_pred3_bupd.
    intros ? ? H1 ? ? H2.
    repeat (f_equiv || apply H1 || apply H2).
  Qed.
  Global Instance bi_pred3_bupd_proper (X1 X2 X3 : ofe) :
    Proper ((≡) ==> (≡)) $
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

  Global Instance bi_pred2_wand_bupd_ne (X1 X2 : ofe) n :
    Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) $
    (===∗@{X1 -d> X2 -d> PROP})%I.
  Proof.
    solve_proper.
  Qed.
  Global Instance bi_pred2_wand_bupd_proper (X1 X2 : ofe) :
    Proper ((≡) ==> (≡) ==> (≡)) $
    (===∗@{X1 -d> X2 -d> PROP})%I.
  Proof.
    solve_proper.
  Qed.
  Lemma bi_pred2_wand_wand_bupd X1 X2 (Φ1 Φ2 : X1 → X2 → PROP) :
    ⊢ (Φ1 --∗ Φ2) -∗ (Φ1 ===∗ Φ2).
  Proof.
    iIntros "H" (? ?) "? !>". by iApply "H".
  Qed.

  Global Instance bi_pred3_wand_bupd_ne (X1 X2 X3 : ofe) n :
    Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) $
    (===∗@{X1 -d> X2 -d> X3 -d> PROP})%I.
  Proof.
    solve_proper.
  Qed.
  Global Instance bi_pred3_wand_bupd_proper (X1 X2 X3 : ofe) :
    Proper ((≡) ==> (≡) ==> (≡)) $
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

Class BiSimilar PROP X Y :=
  bi_similar : X → Y → PROP.
Infix "≈" := bi_similar
( at level 70,
  no associativity
) : bi_scope.
Infix "{ X }@≈@{ Y }" := (@bi_similar _ X Y _)
( at level 70,
  no associativity,
  only parsing
) : bi_scope.
Notation "(≈)" := bi_similar
( only parsing
) : bi_scope.
Notation "({ X }@≈@{ Y } )" := (@bi_similar _ X Y _)
( only parsing
) : bi_scope.
Notation "( x ≈.)" := (bi_similar x)
( only parsing
) : bi_scope.
Notation "(.≈ y )" := (λ x, bi_similar x y)
( only parsing
) : bi_scope.

Global Instance prod_bi_similar `{BiSimilar PROP X1 Y1} `{BiSimilar PROP X2 Y2}
: BiSimilar PROP (X1 * X2) (Y1 * Y2)
:= (
  λ '(x1, x2) '(y1, y2),
    x1 ≈ y1 ∗ x2 ≈ y2
)%I.
Global Instance prod_bi_similar_persistent
  `{BiSimilar PROP X1 Y1} `{BiSimilar PROP X2 Y2}
  `{∀ x1 y1, Persistent (x1 ≈ y1)} `{∀ x2 y2, Persistent (x2 ≈ y2)}
  x1 x2 y1 y2 :
    Persistent ((x1, x2) ≈ (y1, y2)).
Proof.
  apply _.
Qed.

Class BiPaired PROP X Y :=
  bi_paired : X → Y → PROP.
Infix "⟷" := bi_paired
( at level 70,
  no associativity
) : bi_scope.
Infix "{ X }@⟷@{ Y }" := (@bi_paired _ X Y _)
( at level 70,
  no associativity,
  only parsing
) : bi_scope.
Notation "(⟷)" := bi_paired
( only parsing
) : bi_scope.
Notation "({ X }@⟷@{ Y } )" := (@bi_paired _ X Y _)
( only parsing
) : bi_scope.
Notation "( x ⟷.)" := (bi_paired x)
( only parsing
) : bi_scope.
Notation "(.⟷ y )" := (λ x, bi_paired x y)
( only parsing
) : bi_scope.

Global Instance prod_bi_paired `{BiPaired PROP X1 Y1} `{BiPaired PROP X2 Y2}
: BiPaired PROP (X1 * X2) (Y1 * Y2)
:= (
  λ '(x1, x2) '(y1, y2),
    x1 ⟷ y1 ∗ x2 ⟷ y2
)%I.

Class BiWellFormed PROP X :=
  bi_well_formed : X → PROP.

Class BiMapsto PROP loc val :=
  bi_mapsto : loc → dfrac → val → PROP.
Notation "l ↦{ dq } v" := (bi_mapsto l dq v)
( at level 20,
  format "l  ↦{ dq }  v"
) : bi_scope.

Class BiMapstoAny PROP loc :=
  bi_mapsto_any : loc → dfrac → PROP.
Notation "l ↦{ dq }-" := (bi_mapsto_any l dq)
( at level 20,
  format "l  ↦{ dq }-"
) : bi_scope.
Global Instance default_bi_mapsto_any `{BiMapsto PROP loc val}
: BiMapstoAny PROP loc
:= (λ l dq, ∃ v, l ↦{dq} v)%I.

Class BiMapstoDiscarded PROP loc val :=
  bi_mapsto_discarded : loc → val → PROP.
Notation "l ↦□ v" := (bi_mapsto_discarded l v)
( at level 20,
  format "l  ↦□  v"
) : bi_scope.
Global Instance default_bi_mapsto_discarded `{BiMapsto PROP loc val}
: BiMapstoDiscarded PROP loc val
:= (λ l v, l ↦{DfracDiscarded} v)%I.

Class BiMapstoDiscardedAny PROP loc :=
  bi_mapsto_discarded_any : loc → PROP.
Notation "l ↦□-" := (bi_mapsto_discarded_any l)
( at level 20,
  format "l  ↦□-"
) : bi_scope.
Global Instance default_bi_mapsto_discarded_any `{BiMapsto PROP loc val}
: BiMapstoDiscardedAny PROP loc
:= (λ l, ∃ v, l ↦□ v)%I.

Class BiMapstoOwn PROP loc val :=
  bi_mapsto_own : loc → Qp → val → PROP.
Notation "l ↦{# q } v" := (bi_mapsto_own l q v)
( at level 20,
  format "l  ↦{# q }  v"
) : bi_scope.
Global Instance default_bi_mapsto_own `{BiMapsto PROP loc val}
: BiMapstoOwn PROP loc val
:= (λ l q v, l ↦{DfracOwn q} v)%I.

Class BiMapstoOwnAny PROP loc :=
  bi_mapsto_own_any : loc → Qp → PROP.
Notation "l ↦{# q }-" := (bi_mapsto_own_any l q)
( at level 20,
  format "l  ↦{# q }-"
) : bi_scope.
Global Instance default_bi_mapsto_own_any `{BiMapsto PROP loc val}
: BiMapstoOwnAny PROP loc
:= (λ l q, ∃ v, l ↦{#q} v)%I.

Class BiMapstoExcl PROP loc val :=
  bi_mapsto_excl : loc → val → PROP.
Notation "l ↦ v" := (bi_mapsto_excl l v)
( at level 20,
  format "l  ↦  v"
) : bi_scope.
Global Instance default_bi_mapsto_excl `{BiMapsto PROP loc val}
: BiMapstoExcl PROP loc val
:= (λ l v, l ↦{DfracOwn 1} v)%I.

Class BiMapstoExclAny PROP loc :=
  bi_mapsto_excl_any : loc → PROP.
Notation "l ↦-" := (bi_mapsto_excl_any l)
( at level 20,
  format "l  ↦-"
) : bi_scope.
Global Instance default_bi_mapsto_excl_any `{BiMapsto PROP loc val}
: BiMapstoExclAny PROP loc
:= (λ l, ∃ v, l ↦ v)%I.

Class BiMapstoₜ PROP loc val :=
  bi_mapstoₜ : loc → dfrac → val → PROP.
Notation "l ↦ₜ{ dq } v" := (bi_mapstoₜ l dq v)
( at level 20,
  format "l  ↦ₜ{ dq }  v"
) : bi_scope.

Class BiMapstoAnyₜ PROP loc :=
  bi_mapsto_anyₜ : loc → dfrac → PROP.
Notation "l ↦ₜ{ dq }-" := (bi_mapsto_anyₜ l dq)
( at level 20,
  format "l  ↦ₜ{ dq }-"
) : bi_scope.
Global Instance default_bi_mapsto_anyₜ `{BiMapstoₜ PROP loc val}
: BiMapstoAnyₜ PROP loc
:= (λ l dq, ∃ v, l ↦ₜ{dq} v)%I.

Class BiMapstoDiscardedₜ PROP loc val :=
  bi_mapsto_discardedₜ : loc → val → PROP.
Notation "l ↦ₜ□ v" := (bi_mapsto_discardedₜ l v)
( at level 20,
  format "l  ↦ₜ□  v"
) : bi_scope.
Global Instance default_bi_mapsto_discardedₜ `{BiMapstoₜ PROP loc val}
: BiMapstoDiscardedₜ PROP loc val
:= (λ l v, l ↦ₜ{DfracDiscarded} v)%I.

Class BiMapstoDiscardedAnyₜ PROP loc :=
  bi_mapsto_discarded_anyₜ : loc → PROP.
Notation "l ↦ₜ□-" := (bi_mapsto_discarded_anyₜ l)
( at level 20,
  format "l  ↦ₜ□-"
) : bi_scope.
Global Instance default_bi_mapsto_discarded_anyₜ `{BiMapstoₜ PROP loc val}
: BiMapstoDiscardedAnyₜ PROP loc
:= (λ l, ∃ v, l ↦ₜ□ v)%I.

Class BiMapstoOwnₜ PROP loc val :=
  bi_mapsto_ownₜ : loc → Qp → val → PROP.
Notation "l ↦ₜ{# q } v" := (bi_mapsto_ownₜ l q v)
( at level 20,
  format "l  ↦ₜ{# q }  v"
) : bi_scope.
Global Instance default_bi_mapsto_ownₜ `{BiMapstoₜ PROP loc val}
: BiMapstoOwnₜ PROP loc val
:= (λ l q v, l ↦ₜ{DfracOwn q} v)%I.

Class BiMapstoOwnAnyₜ PROP loc :=
  bi_mapsto_own_anyₜ : loc → Qp → PROP.
Notation "l ↦ₜ{# q }-" := (bi_mapsto_own_anyₜ l q)
( at level 20,
  format "l  ↦ₜ{# q }-"
) : bi_scope.
Global Instance default_bi_mapsto_own_anyₜ `{BiMapstoₜ PROP loc val}
: BiMapstoOwnAnyₜ PROP loc
:= (λ l q, ∃ v, l ↦ₜ{#q} v)%I.

Class BiMapstoExclₜ PROP loc val :=
  bi_mapsto_exclₜ : loc → val → PROP.
Notation "l ↦ₜ v" := (bi_mapsto_exclₜ l v)
( at level 20,
  format "l  ↦ₜ  v"
) : bi_scope.
Global Instance default_bi_mapsto_exclₜ `{BiMapstoₜ PROP loc val}
: BiMapstoExclₜ PROP loc val
:= (λ l v, l ↦ₜ{DfracOwn 1} v)%I.

Class BiMapstoExclAnyₜ PROP loc :=
  bi_mapsto_excl_anyₜ : loc → PROP.
Notation "l ↦ₜ-" := (bi_mapsto_excl_anyₜ l)
( at level 20,
  format "l  ↦ₜ-"
) : bi_scope.
Global Instance default_bi_mapsto_excl_anyₜ `{BiMapstoₜ PROP loc val}
: BiMapstoExclAnyₜ PROP loc
:= (λ l, ∃ v, l ↦ₜ v)%I.

Class BiMapstoₛ PROP loc val :=
  bi_mapstoₛ : loc → dfrac → val → PROP.
Notation "l ↦ₛ{ dq } v" := (bi_mapstoₛ l dq v)
( at level 20,
  format "l  ↦ₛ{ dq }  v"
) : bi_scope.

Class BiMapstoAnyₛ PROP loc :=
  bi_mapsto_anyₛ : loc → dfrac → PROP.
Notation "l ↦ₛ{ dq }-" := (bi_mapsto_anyₛ l dq)
( at level 20,
  format "l  ↦ₛ{ dq }-"
) : bi_scope.
Global Instance default_bi_mapsto_anyₛ `{BiMapstoₛ PROP loc val}
: BiMapstoAnyₛ PROP loc
:= (λ l dq, ∃ v, l ↦ₛ{dq} v)%I.

Class BiMapstoDiscardedₛ PROP loc val :=
  bi_mapsto_discardedₛ : loc → val → PROP.
Notation "l ↦ₛ□ v" := (bi_mapsto_discardedₛ l v)
( at level 20,
  format "l  ↦ₛ□  v"
) : bi_scope.
Global Instance default_bi_mapsto_discardedₛ `{BiMapstoₛ PROP loc val}
: BiMapstoDiscardedₛ PROP loc val
:= (λ l v, l ↦ₛ{DfracDiscarded} v)%I.

Class BiMapstoDiscardedAnyₛ PROP loc :=
  bi_mapsto_discarded_anyₛ : loc → PROP.
Notation "l ↦ₛ□-" := (bi_mapsto_discarded_anyₛ l)
( at level 20,
  format "l  ↦ₛ□-"
) : bi_scope.
Global Instance default_bi_mapsto_discarded_anyₛ `{BiMapstoₛ PROP loc val}
: BiMapstoDiscardedAnyₛ PROP loc
:= (λ l, ∃ v, l ↦ₛ□ v)%I.

Class BiMapstoOwnₛ PROP loc val :=
  bi_mapsto_ownₛ : loc → Qp → val → PROP.
Notation "l ↦ₛ{# q } v" := (bi_mapsto_ownₛ l q v)
( at level 20,
  format "l  ↦ₛ{# q }  v"
) : bi_scope.
Global Instance default_bi_mapsto_ownₛ `{BiMapstoₛ PROP loc val}
: BiMapstoOwnₛ PROP loc val
:= (λ l q v, l ↦ₛ{DfracOwn q} v)%I.

Class BiMapstoOwnAnyₛ PROP loc :=
  bi_mapsto_own_anyₛ : loc → Qp → PROP.
Notation "l ↦ₛ{# q }-" := (bi_mapsto_own_anyₛ l q)
( at level 20,
  format "l  ↦ₛ{# q }-"
) : bi_scope.
Global Instance default_bi_mapsto_own_anyₛ `{BiMapstoₛ PROP loc val}
: BiMapstoOwnAnyₛ PROP loc
:= (λ l q, ∃ v, l ↦ₛ{#q} v)%I.

Class BiMapstoExclₛ PROP loc val :=
  bi_mapsto_exclₛ : loc → val → PROP.
Notation "l ↦ₛ v" := (bi_mapsto_exclₛ l v)
( at level 20,
  format "l  ↦ₛ  v"
) : bi_scope.
Global Instance default_bi_mapsto_exclₛ `{BiMapstoₛ PROP loc val}
: BiMapstoExclₛ PROP loc val
:= (λ l v, l ↦ₛ{DfracOwn 1} v)%I.

Class BiMapstoExclAnyₛ PROP loc :=
  bi_mapsto_excl_anyₛ : loc → PROP.
Notation "l ↦ₛ-" := (bi_mapsto_excl_anyₛ l)
( at level 20,
  format "l  ↦ₛ-"
) : bi_scope.
Global Instance default_bi_mapsto_excl_anyₛ `{BiMapstoₛ PROP loc val}
: BiMapstoExclAnyₛ PROP loc
:= (λ l, ∃ v, l ↦ₛ v)%I.
