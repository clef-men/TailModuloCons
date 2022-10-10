From stdpp Require Export
  gmap.

From simuliris.common Require Import
  prelude.
From simuliris.without_calls.tmc Require Export
  lang.notations.

Definition state := gmap loc val.

Global Instance state_eq_dec :
  EqDecision state.
Proof.
  solve_decision.
Defined.
Global Instance state_inhabited :
  Inhabited state.
Proof.
  apply _.
Qed.

Canonical Structure stateO := leibnizO state.

Implicit Types blk : block.
Implicit Types i : index.
Implicit Types l : loc.
Implicit Types v : val.
Implicit Types vs : val * val.
Implicit Types e : expr.
Implicit Types σ : state.

Global Instance block_state_lookup : Lookup block (val * val) state :=
  λ blk σ,
    match σ !! (blk, 𝟙), σ !! (blk, 𝟚) with
    | Some v1, Some v2 => Some (v1, v2)
    | _, _ => None
    end.
Lemma block_state_lookup_None blk σ :
  σ !! blk = None ↔
  ∃ i, σ !! (blk, i) = None.
Proof.
  rewrite {1}/lookup /block_state_lookup.
  split; [| intros [[]]];
    destruct (σ !! (blk, 𝟙)) eqn:?, (σ !! (blk, 𝟚)) eqn:?; naive_solver.
Qed.
Lemma block_state_lookup_Some blk σ vs :
  σ !! blk = Some vs ↔
  σ !! (blk, 𝟙) = Some vs.1 ∧ σ !! (blk, 𝟚) = Some vs.2.
Proof.
  rewrite {1}/lookup /block_state_lookup.
  destruct vs. split;
    intros Heq;
    destruct (σ !! (blk, 𝟙)) eqn:Heq1, (σ !! (blk, 𝟚)) eqn:Heq2;
    rewrite ?Heq in Heq1, Heq2;
    naive_solver.
Qed.

Global Instance block_state_insert : Insert block (val * val) state :=
  λ blk '(v1, v2) σ,
    <[(blk, 𝟚) := v2]> $ <[(blk, 𝟙) := v1]> σ.

Global Instance loc_state_elem_of : ElemOf loc state :=
  λ l σ,
    is_Some (σ !! l).
Global Instance block_state_elem_of : ElemOf block state :=
  λ blk σ,
    ∃ i, (blk, i) ∈ σ.
Lemma loc_elem_of_state l σ :
  l ∈ σ ↔
  is_Some (σ !! l).
Proof.
  done.
Qed.
Lemma loc_not_elem_of_state l σ :
  l ∉ σ ↔
  σ !! l = None.
Proof.
  rewrite eq_None_not_Some. done.
Qed.
Lemma block_elem_of_state blk σ :
  blk ∈ σ ↔
  ∃ i, (blk, i) ∈ σ.
Proof.
  done.
Qed.
Lemma block_not_elem_of_state blk σ :
  blk ∉ σ ↔
  (blk, 𝟙) ∉ σ ∧ (blk, 𝟚) ∉ σ.
Proof.
  rewrite block_elem_of_state. split; [| intros ? [[]]]; naive_solver.
Qed.

Global Instance block_state_fresh : Fresh block state :=
  λ σ,
    fresh $ dom (gset _) σ.
Lemma fresh_block_not_elem_of_state σ :
  fresh σ ∉ σ.
Proof.
  intros [? ?%elem_of_dom]. eapply block_locset_fresh_spec. eexists. done.
Qed.

Inductive head_step : expr → state → expr → state → Prop :=
  | head_step_pair_1 e1 e2 σ :
      head_step
        (e1, e2) σ
        (let: e1 in let: e2.[ren (+1)] in ⟨&1, &0⟩) σ
  | head_step_pair_2 e1 e2 σ :
      head_step
        (e1, e2) σ
        (let: e2 in let: e1.[ren (+1)] in ⟨&0, &1⟩) σ
  | head_step_pair_det v1 v2 blk σ σ' :
      blk ∉ σ →
      σ' = <[blk := (v1, v2)]> σ →
      head_step
        ⟨v1, v2⟩ σ
        blk σ'
  | head_step_let v e e' σ :
      e' = e.[#v/] →
      head_step
        (let: v in e) σ
        e' σ
  | head_step_match_unit e1 e2 σ :
      head_step
        match: () with () => e1 | _ => e2 end σ
        e1 σ
  | head_step_match_loc blk vs e1 e2 e2' σ :
      σ !! blk = Some vs →
      e2' = e2.[#vs.2, #vs.1/] →
      head_step
        match: blk with () => e1 | _ => e2 end σ
        e2' σ
  | head_step_store blk i v σ σ' :
      (blk, i) ∈ σ →
      σ' = <[(blk, i) := v]> σ →
      head_step
        (blk .# i <- v) σ
        #() σ'.

Lemma head_step_pair_det' v1 v2 σ σ' :
  let blk : block := fresh σ in
  σ' = <[blk := (v1, v2)]> σ →
  head_step
    ⟨v1, v2⟩ σ
    blk σ'.
Proof.
  eauto using head_step_pair_det, fresh_block_not_elem_of_state.
Qed.
