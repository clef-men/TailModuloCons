From simuliris.common Require Import
  prelude.
From simuliris.without_calls.tmc Require Export
  simul.simul
  simul.bisubst.

Class CSimul (PROP : bi) exprₜ exprₛ :=
  csimul : (exprₜ → exprₛ → PROP) → exprₜ → exprₛ → PROP.
Notation "'CSIM' eₜ '≲' eₛ '{{' Φ } }" := (csimul Φ eₜ%V%E eₛ%V%E)
( at level 70,
  eₜ, eₛ, Φ at level 200,
  format "'[hv' 'CSIM'  eₜ  ≲  '/   ' eₛ  '/' {{  '[ ' Φ  ']' } } ']'"
) : bi_scope.

Section tmc_simul_heap.
  Context `{TmcSimulHeapGS Σ}.
  Implicit Types v vₜ vₛ : val.
  Implicit Types e eₜ eₛ : expr.
  Implicit Types Γ : bisubst.

  Global Instance tmc_csimul : CSimul _ expr expr := (
    λ Φ eₜ eₛ,
      ∀ Γ, bi_well_formed Γ -∗
      SIM eₜ.[Γ.ₜ#] ≲ eₛ.[Γ.ₛ#] {{ Φ }}
  )%I.
End tmc_simul_heap.
