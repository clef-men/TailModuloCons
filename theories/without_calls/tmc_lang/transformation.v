From tmc.common Require Import
  prelude.
From tmc.without_calls.tmc_lang Require Export
  syntax
  notations
  semantics.

Section direct_dps.
  Local Open Scope index_scope.
  Local Open Scope val_scope.
  Local Open Scope expr_scope.

  Inductive direct : expr → expr → Prop :=
    | DirectVar x :
        direct
          &x
          &x
    | DirectVal v :
        direct
          #v
          #v
    | DirectFail :
        direct
          fail
          fail
    | DirectPair eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ1 eₜ1 →
        direct eₛ2 eₜ2 →
        direct
          (eₛ1, eₛ2)
          (eₜ1, eₜ2)
    | DirectPairDet eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ1 eₜ1 →
        direct eₛ2 eₜ2 →
        direct
          ⟨eₛ1, eₛ2⟩
          ⟨eₜ1, eₜ2⟩
    | DirectLet eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ1 eₜ1 →
        direct eₛ2 eₜ2 →
        direct
          (let: eₛ1 in eₛ2)
          (let: eₜ1 in eₜ2)
    | DirectMatch eₛ0 eₜ0 eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ0 eₜ0 →
        direct eₛ1 eₜ1 →
        direct eₛ2 eₜ2 →
        direct
          match: eₛ0 with () => eₛ1 | _ => eₛ2 end
          match: eₜ0 with () => eₜ1 | _ => eₜ2 end
    | DirectAssign eₛ1 eₜ1 eₛ2 eₜ2 eₛ3 eₜ3 :
        direct eₛ1 eₜ1 →
        direct eₛ2 eₜ2 →
        direct eₛ3 eₜ3 →
        direct
          (eₛ1 .# eₛ2 <- eₛ3)
          (eₜ1 .# eₜ2 <- eₜ3)
    | DirectPairDPS1 eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ1 eₜ1 →
        dps &0 𝟚 eₛ2.[ren (+1)] eₜ2 →
        direct
          (eₛ1, eₛ2)
          (let: (eₜ1, ()) in eₜ2 ;; &0)
    | DirectPairDPS2 eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ2 eₜ2 →
        dps &0 𝟙 eₛ1.[ren (+1)] eₜ1 →
        direct
          (eₛ1, eₛ2)
          (let: ((), eₜ2) in eₜ1 ;; &0)
  with dps : expr → expr → expr → expr → Prop :=
    | DpsBase dst i eₛ eₜ :
        direct eₛ eₜ →
        dps dst i
          eₛ
          (dst .# i <- eₜ)
    | DpsFail dst i :
        dps dst i
          fail
          fail
    | DpsPair1 dst i eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ1 eₜ1 →
        dps &0 𝟚 eₛ2.[ren (+1)] eₜ2 →
        dps dst i
          (eₛ1, eₛ2)
          (let: (eₜ1, ()) in dst.[ren (+1)] .# i.[ren (+1)] <- &0 ;; eₜ2)
    | DpsPair2 dst i eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ2 eₜ2 →
        dps &0 𝟙 eₛ1.[ren (+1)] eₜ1 →
        dps dst i
          (eₛ1, eₛ2)
          (let: ((), eₜ2) in dst.[ren (+1)] .# i.[ren (+1)] <- &0 ;; eₜ1)
    | DpsLet dst i eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ1 eₜ1 →
        dps dst.[ren (+1)] i.[ren (+1)] eₛ2 eₜ2 →
        dps dst i
          (let: eₛ1 in eₛ2)
          (let: eₜ1 in eₜ2)
    | DpsMatch dst i eₛ0 eₜ0 eₛ1 eₜ1 eₛ2 eₜ2 :
        direct eₛ0 eₜ0 →
        dps dst i eₛ1 eₜ1 →
        dps dst.[ren (+2)] i.[ren (+2)] eₛ2 eₜ2 →
        dps dst i
          match: eₛ0 with () => eₛ1 | _ => eₛ2 end
          match: eₜ0 with () => eₜ1 | _ => eₜ2 end.
End direct_dps.

Scheme direct_dps_ind := Minimality for direct Sort Prop
with dps_direct_ind := Minimality for dps Sort Prop.
Combined Scheme direct_dps_mutind from direct_dps_ind, dps_direct_ind.

Create HintDb direct_dps.
#[export] Hint Constructors direct : direct_dps.
#[export] Hint Constructors dps : direct_dps.

Lemma direct_refl e :
  direct e e.
Proof.
  induction e; eauto with direct_dps.
Qed.
#[export] Hint Resolve direct_refl : direct_dps.

Lemma direct_dps_subst :
    (∀ eₛ eₜ, direct eₛ eₜ → ∀ ς, direct eₛ.[ς] eₜ.[ς])
  ∧ (∀ dst i eₛ eₜ, dps dst i eₛ eₜ → ∀ ς, dps dst.[ς] i.[ς] eₛ.[ς] eₜ.[ς]).
Proof.
  apply direct_dps_mutind; eauto with direct_dps;
  try (
    intros * Hdir IHdir Hdps IHdps *;
    specialize (IHdps $ up ς); rewrite !subst_comp !up_lift1 -!subst_comp in IHdps;
    asimpl; rewrite -?subst_comp;
    constructor; auto
  ).
  intros * Hdir0 IHdir0 Hdps1 IHdps1 Hdps2 IHdps2 *.
  specialize (IHdps2 (upn 2 ς)). rewrite !subst_comp !up_liftn -!subst_comp in IHdps2.
  constructor; auto.
Qed.
Lemma direct_subst ς eₛ eₜ :
  direct eₛ eₜ → direct eₛ.[ς] eₜ.[ς].
Proof.
  eauto using (@proj1 _ _ direct_dps_subst).
Qed.
#[export] Hint Resolve direct_subst : direct_dps.
Lemma dps_subst ς dst i eₛ eₜ :
  dps dst i eₛ eₜ →
  dps dst.[ς] i.[ς] eₛ.[ς] eₜ.[ς].
Proof.
  eauto using (@proj2 _ _ direct_dps_subst).
Qed.
#[export] Hint Resolve dps_subst : direct_dps.
