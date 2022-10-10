From stdpp Require Import
  countable
  infinite
  gmap.

From iris.algebra Require Import
  ofe.

From simuliris.common Require Import
  prelude.

(* ---------- block ---------- *)

Definition block := positive.

(* ---------- index ---------- *)

Inductive index := one | two.

Global Instance index_pair_lookup_total X : LookupTotal index X (X * X) :=
  λ i p,
    match i with
    | one => p.1
    | two => p.2
    end.

Global Instance index_eq_dec :
  EqDecision index.
Proof.
  solve_decision.
Qed.
Global Instance index_inhabited : Inhabited index :=
  populate one.
Global Instance index_countable :
  Countable index.
Proof.
  apply (
    inj_countable (
      λ i,
        match i with
        | one => true
        | two => false
        end
    ) (
      λ n,
        match n with
        | true => Some one
        | false => Some two
        end
    )
  ).
  intros []; eauto.
Qed.

(* ---------- loc ---------- *)

Definition loc : Type := block * index.

Global Instance block_locset_elem_of : ElemOf block (gset loc) :=
  λ blk locs,
    ∃ i, (blk, i) ∈ locs.

Global Instance block_locset_fresh : Fresh block (gset loc) :=
  λ locs,
    fresh (elements locs).*1.
Lemma block_locset_fresh_spec (locs : gset loc) :
  fresh locs ∉ locs.
Proof.
  intros [i ?%elem_of_elements%(elem_of_list_fmap_1 fst)].
  eapply infinite_is_fresh. eauto.
Qed.

Canonical locO := leibnizO loc.
