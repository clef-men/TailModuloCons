From simuliris.common Require Import
  prelude
  tactics.
From simuliris.without_calls.tmc Require Export
  lang.lang.

Inductive tmc_dir : expr → expr → Prop :=
  | tmc_dir_var x :
      tmc_dir
        &x
        &x
  | tmc_dir_val v :
      tmc_dir
        #v
        #v
  | tmc_dir_fail :
      tmc_dir
        fail
        fail
  | tmc_dir_pair eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ1 eₜ1 →
      tmc_dir eₛ2 eₜ2 →
      tmc_dir
        (eₛ1, eₛ2)
        (eₜ1, eₜ2)
  | tmc_dir_pair_det eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ1 eₜ1 →
      tmc_dir eₛ2 eₜ2 →
      tmc_dir
        ⟨eₛ1, eₛ2⟩
        ⟨eₜ1, eₜ2⟩
  | tmc_dir_let eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ1 eₜ1 →
      tmc_dir eₛ2 eₜ2 →
      tmc_dir
        (let: eₛ1 in eₛ2)
        (let: eₜ1 in eₜ2)
  | tmc_dir_match eₛ0 eₜ0 eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ0 eₜ0 →
      tmc_dir eₛ1 eₜ1 →
      tmc_dir eₛ2 eₜ2 →
      tmc_dir
        match: eₛ0 with () => eₛ1 | _ => eₛ2 end
        match: eₜ0 with () => eₜ1 | _ => eₜ2 end
  | tmc_dir_store eₛ1 eₜ1 eₛ2 eₜ2 eₛ3 eₜ3 :
      tmc_dir eₛ1 eₜ1 →
      tmc_dir eₛ2 eₜ2 →
      tmc_dir eₛ3 eₜ3 →
      tmc_dir
        (eₛ1 .# eₛ2 <- eₛ3)
        (eₜ1 .# eₜ2 <- eₜ3)
  | tmc_dir_pair_dps_1 eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ1 eₜ1 →
      tmc_dps &0 𝟚 eₛ2.[ren (+1)] eₜ2 →
      tmc_dir
        (eₛ1, eₛ2)
        (let: (eₜ1, ()) in eₜ2 ;; &0)
  | tmc_dir_pair_dps_2 eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ2 eₜ2 →
      tmc_dps &0 𝟙 eₛ1.[ren (+1)] eₜ1 →
      tmc_dir
        (eₛ1, eₛ2)
        (let: ((), eₜ2) in eₜ1 ;; &0)
with tmc_dps : expr → expr → expr → expr → Prop :=
  | tmc_dps_base dst i eₛ eₜ :
      tmc_dir eₛ eₜ →
      tmc_dps dst i
        eₛ
        (dst .# i <- eₜ)
  | tmc_dps_fail dst i :
      tmc_dps dst i
        fail
        fail
  | tmc_dps_pair_1 dst i eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ1 eₜ1 →
      tmc_dps &0 𝟚 eₛ2.[ren (+1)] eₜ2 →
      tmc_dps dst i
        (eₛ1, eₛ2)
        (let: (eₜ1, ()) in dst.[ren (+1)] .# i.[ren (+1)] <- &0 ;; eₜ2)
  | tmc_dps_pair_2 dst i eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ2 eₜ2 →
      tmc_dps &0 𝟙 eₛ1.[ren (+1)] eₜ1 →
      tmc_dps dst i
        (eₛ1, eₛ2)
        (let: ((), eₜ2) in dst.[ren (+1)] .# i.[ren (+1)] <- &0 ;; eₜ1)
  | tmc_dps_let dst i eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ1 eₜ1 →
      tmc_dps dst.[ren (+1)] i.[ren (+1)] eₛ2 eₜ2 →
      tmc_dps dst i
        (let: eₛ1 in eₛ2)
        (let: eₜ1 in eₜ2)
  | tmc_dps_match dst i eₛ0 eₜ0 eₛ1 eₜ1 eₛ2 eₜ2 :
      tmc_dir eₛ0 eₜ0 →
      tmc_dps dst i eₛ1 eₜ1 →
      tmc_dps dst.[ren (+2)] i.[ren (+2)] eₛ2 eₜ2 →
      tmc_dps dst i
        match: eₛ0 with () => eₛ1 | _ => eₛ2 end
        match: eₜ0 with () => eₜ1 | _ => eₜ2 end.

Scheme tmc_dir_dps_ind := Minimality for tmc_dir Sort Prop
with tmc_dps_dir_ind := Minimality for tmc_dps Sort Prop.
Combined Scheme tmc_ind from tmc_dir_dps_ind, tmc_dps_dir_ind.

Create HintDb tmc.
#[export] Hint Constructors tmc_dir : tmc.
#[export] Hint Constructors tmc_dps : tmc.

Lemma tmc_dir_refl e :
  tmc_dir e e.
Proof.
  induction e; eauto with tmc.
Qed.
#[export] Hint Resolve tmc_dir_refl : tmc.

Lemma tmc_subst :
  ( ∀ eₛ eₜ,
    tmc_dir eₛ eₜ →
    ∀ ς, tmc_dir eₛ.[ς] eₜ.[ς]
  ) ∧ (
    ∀ dst i eₛ eₜ,
    tmc_dps dst i eₛ eₜ →
    ∀ ς, tmc_dps dst.[ς] i.[ς] eₛ.[ς] eₜ.[ς]
  ).
Proof.
  apply tmc_ind; eauto with tmc;
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
Lemma tmc_dir_subst ς eₛ eₜ :
  tmc_dir eₛ eₜ →
  tmc_dir eₛ.[ς] eₜ.[ς].
Proof.
  eauto using (proj1 tmc_subst).
Qed.
#[export] Hint Resolve tmc_dir_subst : tmc.
Lemma tmc_dps_subst ς dst i eₛ eₜ :
  tmc_dps dst i eₛ eₜ →
  tmc_dps dst.[ς] i.[ς] eₛ.[ς] eₜ.[ς].
Proof.
  eauto using (proj2 tmc_subst).
Qed.
#[export] Hint Resolve tmc_dps_subst : tmc.

Lemma tmc_dir_ctxi (c : ctxi) eₛ eₜ :
  tmc_dir eₛ eₜ →
  tmc_dir (c @@ eₛ) (c @@ eₜ).
Proof.
  destruct c; eauto with tmc.
Qed.
#[export] Hint Resolve tmc_dir_ctxi : tmc.
Lemma tmc_dir_ctx (C : ctx) eₛ eₜ :
  tmc_dir eₛ eₜ →
  tmc_dir (C @@ eₛ) (C @@ eₜ).
Proof.
  revert eₛ eₜ. induction C; eauto with tmc.
Qed.
#[export] Hint Resolve tmc_dir_ctx : tmc.
