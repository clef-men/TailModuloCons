From stdpp Require Import
  countable.

From iris.algebra Require Export
  ofe.

From Autosubst Require Export
  Autosubst.

From tmc.common Require Import
  prelude.
From tmc.common Require Export
  typeclasses
  loc.

(* ---------- index ---------- *)

Inductive index := one | two.

Global Instance index_lookup_total X : LookupTotal index X (X * X) :=
  λ t p,
    match t with
    | one => p.1
    | two => p.2
    end.

Global Instance index_insert X : Insert index X (X * X) :=
  λ t x p,
    match t with
    | one => (x, p.2)
    | two => (p.1, x)
    end.

Global Instance index_eq_dec : EqDecision index.
Proof.
  solve_decision.
Qed.

Global Instance index_countable : Countable index.
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
  intros []; auto.
Qed.

(* ---------- val ---------- *)

Inductive val :=
  | Loc : loc → val
  | Index : index → val
  | Unit : val.

Global Instance well_formed_val : WellFormed val :=
  λ v,
    match v with
    | Loc _ => False
    | _ => True
    end.

Global Instance val_eq_dec : EqDecision val.
Proof.
  solve_decision.
Qed.

Global Instance val_countable : Countable val.
Proof.
  apply (
    inj_countable' (
      λ v,
        match v with
        | Loc l => inl l
        | Index i => inr (inl i)
        | Unit => inr (inr ())
        end
    ) (
      λ v,
        match v with
        | inl l => Loc l
        | inr (inl i) => Index i
        | inr (inr ()) => Unit
        end
    )
  ).
  intros []; auto.
Qed.

Global Instance val_inhabited : Inhabited val :=
  populate (Unit).

Canonical Structure valO := leibnizO val.

(* ---------- expr ---------- *)

Inductive expr :=
  | Var : var → expr
  | Val : val → expr
  | Fail : expr
  | Pair : expr → expr → expr
  | PairDet : expr → expr → expr
  | Let : expr → {bind expr} → expr
  | Match : expr → expr → {bind 2 of expr} → expr
  | Store : expr → expr → expr → expr.

Global Instance expr_ids : Ids expr. derive. Defined.
Global Instance expr_rename : Rename expr. derive. Defined.
Global Instance expr_subst : Subst expr. derive. Defined.
Global Instance expr_subst_lemmas : SubstLemmas expr. derive. Qed.

Global Instance well_formed_expr : WellFormed expr :=
  fix well_formed e :=
    match e with
    | Var _ => True
    | Val (Loc _) => False
    | Val _ => True
    | Fail => True
    | Pair e1 e2 => well_formed e1 /\ well_formed e2
    | PairDet _ _ => False
    | Let e1 e2 => well_formed e1 /\ well_formed e2
    | Match e0 e1 e2 => well_formed e0 /\ well_formed e1 /\ well_formed e2
    | Store e1 e2 e3 => well_formed e1 /\ well_formed e2 /\ well_formed e3
    end.

Global Instance expr_eq_dec : EqDecision expr.
Proof.
  solve_decision.
Qed.

Global Instance expr_countable : Countable expr.
Proof.
  apply (
    inj_countable' (
      fix enc e :=
        match e with
        | Val v => GenLeaf $ inl v
        | Var x => GenLeaf $ inr $ inl x
        | Fail => GenLeaf $ inr $ inr ()
        | Pair e1 e2 => GenNode 0 [enc e1; enc e2]
        | PairDet e1 e2 => GenNode 1 [enc e1; enc e2]
        | Let e1 e2 => GenNode 2 [enc e1; enc e2]
        | Match e0 e1 e2 => GenNode 3 [enc e0; enc e1; enc e2]
        | Store e1 e2 e3 => GenNode 4 [enc e1; enc e2; enc e3]
        end
    ) (
      fix dec e :=
        match e with
        | GenLeaf (inl v) => Val v
        | GenLeaf (inr (inl x)) => Var x
        | GenLeaf (inr (inr ())) => Fail
        | GenNode 0 [e1; e2] => Pair (dec e1) (dec e2)
        | GenNode 1 [e1; e2] => PairDet (dec e1) (dec e2)
        | GenNode 2 [e1; e2] => Let (dec e1) (dec e2)
        | GenNode 3 [e0; e1; e2] => Match (dec e0) (dec e1) (dec e2)
        | GenNode 4 [e1; e2; e3] => Store (dec e1) (dec e2) (dec e3)
        | _ => Fail
        end
    )
  ).
  intros e. induction e; try congruence.
Qed.

Global Instance expr_inhabited : Inhabited expr :=
  populate (Val inhabitant).

Canonical Structure exprO := leibnizO expr.

(* ---------- ectx_item ---------- *)

Inductive ectx_item :=
  | ECtxLet : expr → ectx_item
  | ECtxMatch : expr → expr → ectx_item
  | ECtxStore1 : expr → expr → ectx_item
  | ECtxStore2 : val → expr → ectx_item
  | ECtxStore3 : val → val → ectx_item.

Global Instance ectx_item_well_formed : WellFormed ectx_item :=
  λ k,
    match k with
    | ECtxLet e2 => well_formed e2
    | ECtxMatch e1 e2 => well_formed e1 /\ well_formed e2
    | ECtxStore1 e2 e3 => well_formed e2 /\ well_formed e3
    | ECtxStore2 v1 e3 => well_formed v1 /\ well_formed e3
    | ECtxStore3 v1 v2 => well_formed v1 /\ well_formed v2
    end.

Definition fill_item k e :=
  match k with
  | ECtxLet e2 =>
      Let e e2
  | ECtxMatch e1 e2 =>
      Match e e1 e2
  | ECtxStore1 e2 e3 =>
      Store e e2 e3
  | ECtxStore2 v1 e3 =>
      Store (Val v1) e e3
  | ECtxStore3 v1 v2 =>
      Store (Val v1) (Val v2) e
  end.

(* ---------- ctx_item ---------- *)

Inductive ctx_item :=
  | CtxPair1 : expr → ctx_item
  | CtxPair2 : expr → ctx_item
  | CtxPairDet1 : expr → ctx_item
  | CtxPairDet2 : expr → ctx_item
  | CtxLetCtx1 : expr → ctx_item
  | CtxLetCtx2 : expr → ctx_item
  | CtxMatch0 : expr → expr → ctx_item
  | CtxMatch1 : expr → expr → ctx_item
  | CtxMatch2 : expr → expr → ctx_item
  | CtxStore1 : expr → expr → ctx_item
  | CtxStore2 : expr → expr → ctx_item
  | CtxStore3 : expr → expr → ctx_item.

Global Instance ctx_item_well_formed : WellFormed ctx_item :=
  λ c,
    match c with
    | CtxPair1 e2 => well_formed e2
    | CtxPair2 e1 => well_formed e1
    | CtxPairDet1 _ => False
    | CtxPairDet2 _ => False
    | CtxLetCtx1 e2 => well_formed e2
    | CtxLetCtx2 e1 => well_formed e1
    | CtxMatch0 e1 e2 => well_formed e1 /\ well_formed e2
    | CtxMatch1 e0 e2 => well_formed e0 /\ well_formed e2
    | CtxMatch2 e0 e1 => well_formed e0 /\ well_formed e1
    | CtxStore1 e2 e3 => well_formed e2 /\ well_formed e3
    | CtxStore2 e1 e3 => well_formed e1 /\ well_formed e3
    | CtxStore3 e1 e2 => well_formed e1 /\ well_formed e2
    end.
