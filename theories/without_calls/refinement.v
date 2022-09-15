From tmc.common Require Export
  prelude.
From tmc.without_calls.language Require Export
  lang.

Section behaviour.
  Context {Λ : lang}.

  Inductive behaviour :=
    | behaviour_converge : expr Λ → behaviour
    | behaviour_diverge : behaviour.

  Inductive has_behaviour e σ : behaviour → Prop :=
    | has_behaviour_converge e' σ' :
        rtc step (e, σ) (e', σ') →
        irreducible e' σ' →
        has_behaviour e σ (behaviour_converge e')
    | has_behaviour_diverge :
        diverge e σ →
        has_behaviour e σ behaviour_diverge.

  Section behaviour_refinement.
    Context `{Equiv (val Λ)}.

    Inductive behaviour_refinement : SqSubsetEq behaviour :=
      | behaviour_refinement_val eₜ vₜ eₛ vₛ :
          eₜ = of_val vₜ →
          eₛ = of_val vₛ →
          vₜ ≡ vₛ →
          behaviour_refinement (behaviour_converge eₜ) (behaviour_converge eₛ)
      | behaviour_refinement_stuck eₜ eₛ :
          to_val eₜ = None →
          to_val eₛ = None →
          behaviour_refinement (behaviour_converge eₜ) (behaviour_converge eₛ)
      | behaviour_refinement_diverge :
          behaviour_refinement behaviour_diverge behaviour_diverge.
    Global Existing Instance behaviour_refinement.

    Lemma behaviour_refinement_strongly_stuck eₜ eₛ :
      strongly_stuck eₜ →
      strongly_stuck eₛ →
      behaviour_converge eₜ ⊑ behaviour_converge eₛ.
    Proof.
      rewrite /strongly_stuck. intros.
      apply behaviour_refinement_stuck; naive_solver.
    Qed.
  End behaviour_refinement.
End behaviour.
