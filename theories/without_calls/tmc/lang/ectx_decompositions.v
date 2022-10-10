From stdpp Require Import
  list.

From simuliris.common Require Import
  prelude
  tactics.
From simuliris.without_calls.tmc Require Export
  lang.lang.

Fixpoint ectx_decompositions e :=
  let ectx_decompositions_with k e :=
    (λ '(K, e), ([k] ⋅ K, e)) <$> ectx_decompositions e
  in
  ([], e) ::
  match e with
  | Var _
  | Val _
  | Fail
  | Pair _ _
  | PairDet _ _ =>
      []
  | Let e1 e2 =>
      ectx_decompositions_with (EctxLet e2) e1
  | Match e0 e1 e2 =>
      ectx_decompositions_with (EctxMatch e1 e2) e0
  | Store e1 e2 e3 =>
      ectx_decompositions_with (EctxStore1 e2 e3) e1 ++
      match to_val e1 with
      | None =>
          []
      | Some v1 =>
          ectx_decompositions_with (EctxStore2 v1 e3) e2 ++
          match to_val e2 with
          | None =>
              []
          | Some v2 =>
              ectx_decompositions_with (EctxStore3 v1 v2) e3
          end
      end
  end.

Lemma ectx_decompositions_sound e K e' :
  (K, e') ∈ ectx_decompositions e →
  e = K @@ e'.
Proof.
  revert K e'. induction e; simpl; intros;
  repeat match goal with
  | _ =>
      progress decompose_elem_of_list
  | H : _ ∈ _ <$> _ |- _ =>
      eapply elem_of_list_fmap in H; simplify
  | H : _ ∈ match to_val ?e with None => _ | Some _ => _ end |- _ =>
      let Heq := fresh "Heq" in
      destruct (to_val e) eqn:Heq; first eapply of_to_val in Heq
  end;
  rewrite -?fill_op; naive_solver.
Qed.

Lemma ectx_decompositions_base e :
  (∅, e) ∈ ectx_decompositions e.
Proof.
  destruct e; econstructor.
Qed.

Lemma ectx_decompositions_complete K e :
  (K, e) ∈ ectx_decompositions $ K @@ e.
Proof.
  revert K e.
  assert (
    ∀ K e,
    (reverse K, e) ∈ ectx_decompositions $ (reverse K) @@ e).
  {
    intros. induction K as [| k K]; first eapply ectx_decompositions_base.
    rewrite reverse_cons -fill_op /=. destruct k; simpl;
    repeat match goal with
    | |- _ ∈ _ :: _ =>
        econstructor
    | |- _ ∈ _ <$> _ =>
        apply elem_of_list_fmap; by exists (reverse K, e)
    | |- _ ∈ _ ++ _ =>
        apply elem_of_app; left
    | _ =>
        simpl
    end.
  }
  intros. by rewrite -(reverse_involutive K).
Qed.
Lemma ectx_decompositions_complete' e K e' :
  e = K @@ e' →
  (K, e') ∈ ectx_decompositions e.
Proof.
  intros ->. eapply ectx_decompositions_complete.
Qed.

Lemma ectx_decompositions_spec e K e' :
  e = K @@ e' ↔
  (K, e') ∈ ectx_decompositions e.
Proof.
  split; eauto using ectx_decompositions_sound, ectx_decompositions_complete'.
Qed.
