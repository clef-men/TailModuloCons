From simuliris.common Require Import
  prelude
  tactics.
From simuliris.without_calls.tmc Require Export
  lang.ectx_decompositions.

Ltac invert_head_step :=
  repeat match goal with
  | _ =>
      progress simplify_map_eq/=
  | H : to_val _ = Some _ |- _ =>
      apply of_to_val in H
  | H : head_step ?e _ _ _ |- _ =>
      try (is_var e; fail 1);
      invert H
  end.

Create HintDb tmc_lang.

#[export] Hint Extern 0 (
  head_reducible _ _
) => (
  apply strongly_head_reducible
) : tmc_lang.
#[export] Hint Extern 1 (
  head_reducible _ _
) => (
  eexists _, _; simpl
) : tmc_lang.
#[export] Hint Extern 0 (
  head_step (PairDet _ _) _ _ _
) => (
  eapply head_step_pair_det'
) : tmc_lang.
#[export] Hint Extern 1 (
  head_step _ _ _ _
) => (
  econstructor
) : tmc_lang.

#[export] Hint Extern 0 (
  sub_redexes_are_values _
) => (
  let Hdecomps := fresh "Hdecomps" in
  intros ?* Hdecomps%ectx_decompositions_spec; invert Hdecomps; first done;
    decompose_elem_of_list; simplify
) : tmc_lang.

#[export] Hint Resolve fresh_block_not_elem_of_state
: tmc_lang.

Ltac unfold_elem_of_state :=
  repeat match goal with H : _ |- _ =>
    first [
      rewrite loc_not_elem_of_state in H
    | rewrite block_not_elem_of_state in H
    | rewrite loc_elem_of_state in H
    | rewrite block_elem_of_state in H
    ]
  end;
  repeat first [
    rewrite loc_not_elem_of_state
  | rewrite block_not_elem_of_state
  | rewrite loc_elem_of_state
  | rewrite block_elem_of_state
  ].
Ltac unfold_state_lookup :=
  repeat match goal with H : _ |- _ =>
    first [
      rewrite block_state_lookup_None in H
    | rewrite block_state_lookup_Some in H
    | rewrite (lookup_insert_None (K := loc) (M := gmap loc) (A := val)) in H
    | rewrite (lookup_insert_Some (K := loc) (M := gmap loc) (A := val)) in H
    | rewrite (lookup_delete_None (K := loc) (M := gmap loc) (A := val)) in H
    | rewrite (lookup_delete_Some (K := loc) (M := gmap loc) (A := val)) in H
    | rewrite (lookup_difference_None (K := loc) (M := gmap loc) (A := val)) in H
    | rewrite (lookup_difference_Some (K := loc) (M := gmap loc) (A := val)) in H
    | rewrite (lookup_intersection_None (K := loc) (M := gmap loc) (A := val)) in H
    | rewrite (lookup_intersection_Some (K := loc) (M := gmap loc) (A := val)) in H
    | rewrite (lookup_union_None (K := loc) (M := gmap loc) (A := val)) in H
    | rewrite (lookup_union_Some (K := loc) (M := gmap loc) (A := val)) in H
    ]
  end;
  repeat first [
    rewrite block_state_lookup_None
  | rewrite block_state_lookup_Some
  | rewrite (lookup_insert_None (K := loc) (M := gmap loc) (A := val))
  | rewrite (lookup_insert_Some (K := loc) (M := gmap loc) (A := val))
  | rewrite (lookup_delete_None (K := loc) (M := gmap loc) (A := val))
  | rewrite (lookup_delete_Some (K := loc) (M := gmap loc) (A := val))
  | rewrite (lookup_difference_None (K := loc) (M := gmap loc) (A := val))
  | rewrite (lookup_difference_Some (K := loc) (M := gmap loc) (A := val))
  | rewrite (lookup_intersection_None (K := loc) (M := gmap loc) (A := val))
  | rewrite (lookup_intersection_Some (K := loc) (M := gmap loc) (A := val))
  | rewrite (lookup_union_None (K := loc) (M := gmap loc) (A := val))
  | rewrite (lookup_union_Some (K := loc) (M := gmap loc) (A := val))
  ].
Ltac unfold_state_eqns :=
  unfold_elem_of_state;
  unfold_state_lookup;
  simplify.
Ltac solve_state_eqn :=
  unfold_state_eqns;
  naive_solver.
#[export] Hint Extern 5 => solve_state_eqn
: tmc_lang.
