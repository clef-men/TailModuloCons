From stdpp Require Export
  gmap.

From tmc.common Require Import
  prelude.
From tmc.without_calls Require Import
  language.lang.
From tmc.without_calls.tmc_lang Require Export
  syntax
  notations.

Definition state := gmap loc (val * val).

Global Instance state_eq_dec : EqDecision state.
Proof.
  solve_decision.
Defined.

Global Instance state_inhabited : Inhabited state.
Proof.
  apply _.
Qed.

Canonical Structure stateO := leibnizO state.

Implicit Types l : loc.
Implicit Types i : index.
Implicit Types v : val.
Implicit Types vs : val * val.
Implicit Types e : expr.
Implicit Types σ : state.

Inductive head_step : expr → state → expr → state → Prop :=
  | StepPair1 e1 e2 σ :
      head_step
        (e1, e2)%E σ
        (let: e1 in let: e2.[ren (+1)] in ⟨&1, &0⟩)%E σ
  | StepPair2 e1 e2 σ :
      head_step
        (e1, e2)%E σ
        (let: e2 in let: e1.[ren (+1)] in ⟨&0, &1⟩)%E σ
  | StepPairDet v1 v2 l σ σ' :
      σ !! l = None →
      σ' = <[l := (v1, v2)]> σ →
      head_step
        ⟨v1, v2⟩%E σ
        l σ'
  | StepLet v e σ :
      head_step
        (let: v in e)%E σ
        e.[#v/] σ
  | StepMatchUnit e1 e2 σ :
      head_step
        (match: #() with () => e1 | _ => e2 end)%E σ
        e1 σ
  | StepMatchLoc l vs e1 e2 σ :
      σ !! l = Some vs →
      head_step
        (match: l with () => e1 | _ => e2 end)%E σ
        e2.[#vs.2, #vs.1/] σ
  | StepStore l i v vs σ σ' :
      σ !! l = Some vs →
      σ' = <[l := <[i := v]> vs]> σ →
      head_step
        (l .# i <- v)%E σ
        #() σ'.
