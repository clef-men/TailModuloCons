From simuliris.common Require Import
  prelude
  typeclasses.
From simuliris.without_calls Require Export
  lang.lang.

Section behaviour.
  Context {Λ : lang}.

  Inductive behaviour :=
    | behaviour_converges : expr Λ → behaviour
    | behaviour_diverges : behaviour.

  Inductive has_behaviour e σ : behaviour → Prop :=
    | has_behaviour_converges e' σ' :
        converges e σ e' σ' →
        has_behaviour e σ (behaviour_converges e')
    | has_behaviour_diverges :
        diverges e σ →
        has_behaviour e σ behaviour_diverges.
End behaviour.
Global Arguments behaviour : clear implicits.

Section refinement.
  Context `{Similar (val Λₜ) (val Λₛ)}.

  Inductive behaviour_refinement : Refines (behaviour Λₜ) (behaviour Λₛ) :=
    | behaviour_refinement_val eₜ vₜ eₛ vₛ :
        eₜ = of_val vₜ →
        eₛ = of_val vₛ →
        vₜ ≈ vₛ →
        behaviour_refinement (behaviour_converges eₜ) (behaviour_converges eₛ)
    | behaviour_refinement_stuck eₜ eₛ :
        to_val eₜ = None →
        to_val eₛ = None →
        behaviour_refinement (behaviour_converges eₜ) (behaviour_converges eₛ)
    | behaviour_refinement_diverges :
        behaviour_refinement behaviour_diverges behaviour_diverges.
  Global Existing Instance behaviour_refinement.

  Global Instance refinement : Refines (cfg Λₜ) (cfg Λₛ) :=
    λ '(eₜ, σₜ) '(eₛ, σₛ),
      ∀ bₜ, has_behaviour eₜ σₜ bₜ →
      ∃ bₛ, has_behaviour eₛ σₛ bₛ ∧ bₜ ⊴ bₛ.
End refinement.

Section crefinement.
  Context {Λ : lang}.
  Context (ctx : Type).
  Context `{Similar (val Λ) (val Λ)} `{Closed (expr Λ)} `{Empty (state Λ)}.
  Context `{LangCtx Λ ctx} `{WellFormed ctx}.

  Global Instance crefinement : Refines (expr Λ) (expr Λ) :=
    λ eₜ eₛ,
      ∀ C, well_formed C →
      closed (C @@ eₜ) →
      closed (C @@ eₛ) →
      (C @@ eₜ, ∅) ⊴ (C @@ eₛ, ∅).
End crefinement.
