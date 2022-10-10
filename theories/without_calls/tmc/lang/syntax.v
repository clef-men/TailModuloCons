From stdpp Require Import
  countable.

From iris.algebra Require Export
  ofe.

From Autosubst Require Export
  Autosubst.

From simuliris.common Require Import
  prelude
  tactics
  relations.
From simuliris.common Require Export
  typeclasses
  loc.

(* ---------- val ---------- *)

Inductive val :=
  | Block : block → val
  | Index : index → val
  | Unit : val.

Global Instance val_well_formed : WellFormed val :=
  λ v,
    match v with
    | Block _ => False
    | _ => True
    end.

Global Instance val_similar : Similar val val :=
  λ vₜ vₛ,
    match vₜ, vₛ with
    | Block _, Block _ => True
    | Index iₜ, Index iₛ => iₜ = iₛ
    | Unit, Unit => True
    | _, _ => False
    end.

Global Instance val_eq_dec :
  EqDecision val.
Proof.
  solve_decision.
Qed.
Global Instance val_countable :
  Countable val.
Proof.
  apply (
    inj_countable' (
      λ v,
        match v with
        | Block blk => inl blk
        | Index i => inr (inl i)
        | Unit => inr (inr ())
        end
    ) (
      λ v,
        match v with
        | inl blk => Block blk
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

Inductive expr_head :=
  | HeadVar : var → expr_head
  | HeadVal : val → expr_head
  | HeadFail : expr_head
  | HeadPair : expr_head
  | HeadPairDet : expr_head
  | HeadLet : expr_head
  | HeadMatch : expr_head
  | HeadStore : expr_head.

Definition expr_split e :=
  match e with
  | Var x => (HeadVar x, [])
  | Val v => (HeadVal v, [])
  | Fail => (HeadFail, [])
  | Pair e1 e2 => (HeadPair, [e1 ; e2])
  | PairDet e1 e2 => (HeadPairDet, [e1 ; e2])
  | Let e1 e2 => (HeadLet, [e1 ; e2])
  | Match e0 e1 e2 => (HeadMatch, [e0 ; e1 ; e2])
  | Store e1 e2 e3 => (HeadStore, [e1 ; e2 ; e3])
  end.

Global Instance expr_head_well_formed : WellFormed expr_head :=
  λ hd,
    match hd with
    | HeadVal (Block _)
    | HeadPairDet => False
    | _ => True
    end.

Global Instance expr_well_formed : WellFormed expr :=
  fix wf e :=
    well_formed (expr_split e).1 ∧
    match e with
    | Pair e1 e2 => wf e1 ∧ wf e2
    | PairDet e1 e2 => wf e1 ∧ wf e2
    | Let e1 e2 => wf e1 ∧ wf e2
    | Match e0 e1 e2 => wf e0 ∧ wf e1 ∧ wf e2
    | Store e1 e2 e3 => wf e1 ∧ wf e2 ∧ wf e3
    | _ => True
    end.

Fixpoint expr_closed_at n e :=
  match e with
  | Var x =>
      x < n
  | Val v =>
      True
  | Fail =>
      True
  | Pair e1 e2 =>
      expr_closed_at n e1 ∧
      expr_closed_at n e2
  | PairDet e1 e2 =>
      expr_closed_at n e1 ∧
      expr_closed_at n e2
  | Let e1 e2 =>
      expr_closed_at n e1 ∧
      expr_closed_at (1 + n) e2
  | Match e0 e1 e2 =>
      expr_closed_at n e0 ∧
      expr_closed_at n e1 ∧
      expr_closed_at (2 + n) e2
  | Store e1 e2 e3 =>
      expr_closed_at n e1 ∧
      expr_closed_at n e2 ∧
      expr_closed_at n e3
  end.
Global Instance expr_closed : Closed expr :=
  expr_closed_at 0.

Global Instance expr_eq_dec :
  EqDecision expr.
Proof.
  solve_decision.
Qed.
Global Instance expr_countable :
  Countable expr.
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

Inductive subexprdir : expr → expr → Prop :=
  | subexprdir_pair_1 e1 e2 :
      subexprdir e1 (Pair e1 e2)
  | subexprdir_pair_2 e1 e2 :
      subexprdir e2 (Pair e1 e2)
  | subexprdir_pair_det_1 e1 e2 :
      subexprdir e1 (PairDet e1 e2)
  | subexprdir_pair_det_2 e1 e2 :
      subexprdir e2 (PairDet e1 e2)
  | subexprdir_let_1 e1 e2 :
      subexprdir e1 (Let e1 e2)
  | subexprdir_let_2 e1 e2 :
      subexprdir e2 (Let e1 e2)
  | subexprdir_match_0 e0 e1 e2 :
      subexprdir e0 (Match e0 e1 e2)
  | subexprdir_match_1 e0 e1 e2 :
      subexprdir e1 (Match e0 e1 e2)
  | subexprdir_match_2 e0 e1 e2 :
      subexprdir e2 (Match e0 e1 e2)
  | subexprdir_store_1 e1 e2 e3 :
      subexprdir e1 (Store e1 e2 e3)
  | subexprdir_store_2 e1 e2 e3 :
      subexprdir e2 (Store e1 e2 e3)
  | subexprdir_store_3 e1 e2 e3 :
      subexprdir e3 (Store e1 e2 e3).
Lemma subexprdir_wf :
  wf subexprdir.
Proof.
  intros e. induction e; econstructor; intros e' He'; invert He'; try naive_solver.
Qed.

Definition subexpr :=
  tc subexprdir.
Global Instance expr_sqsubset : SqSubset expr :=
  subexpr.
Lemma subexpr_wf :
  wf (⊏).
Proof.
  eauto using tc_wf, subexprdir_wf.
Qed.

(* ---------- ectxi ---------- *)

Inductive ectxi :=
  | EctxLet : expr → ectxi
  | EctxMatch : expr → expr → ectxi
  | EctxStore1 : expr → expr → ectxi
  | EctxStore2 : val → expr → ectxi
  | EctxStore3 : val → val → ectxi.

Global Instance ectxi_fill : Fill ectxi expr :=
  λ k e,
    match k with
    | EctxLet e2 =>
        Let e e2
    | EctxMatch e1 e2 =>
        Match e e1 e2
    | EctxStore1 e2 e3 =>
        Store e e2 e3
    | EctxStore2 v1 e3 =>
        Store (Val v1) e e3
    | EctxStore3 v1 v2 =>
        Store (Val v1) (Val v2) e
    end.

Definition ectxi_split k :=
  match k with
  | EctxLet e2 => (HeadLet, [e2])
  | EctxMatch e1 e2 => (HeadMatch, [e1 ; e2])
  | EctxStore1 e2 e3 => (HeadStore, [e2 ; e3])
  | EctxStore2 v1 e3 => (HeadStore, [Val v1 ; e3])
  | EctxStore3 v1 v2 => (HeadStore, [Val v1 ; Val v2])
  end.

Global Instance ectxi_well_formed : WellFormed ectxi :=
  λ k,
    let '(hd, es) := ectxi_split k in
    well_formed hd ∧ Forall well_formed es.

(* ---------- ectx ---------- *)

Notation ectx := (list ectxi).

Global Instance ectx_well_formed : WellFormed ectx :=
  Forall well_formed.

(* ---------- ctxi ---------- *)

Inductive ctxi :=
  | CtxPair1 : expr → ctxi
  | CtxPair2 : expr → ctxi
  | CtxPairDet1 : expr → ctxi
  | CtxPairDet2 : expr → ctxi
  | CtxLet1 : expr → ctxi
  | CtxLet2 : expr → ctxi
  | CtxMatch0 : expr → expr → ctxi
  | CtxMatch1 : expr → expr → ctxi
  | CtxMatch2 : expr → expr → ctxi
  | CtxStore1 : expr → expr → ctxi
  | CtxStore2 : expr → expr → ctxi
  | CtxStore3 : expr → expr → ctxi.

Global Instance ctxi_fill : Fill ctxi expr :=
  λ c e,
    match c with
    | CtxPair1 e2 => Pair e e2
    | CtxPair2 e1 => Pair e1 e
    | CtxPairDet1 e2 => PairDet e e2
    | CtxPairDet2 e1 => PairDet e1 e
    | CtxLet1 e2 => Let e e2
    | CtxLet2 e1 => Let e1 e
    | CtxMatch0 e1 e2 => Match e e1 e2
    | CtxMatch1 e0 e2 => Match e0 e e2
    | CtxMatch2 e0 e1 => Match e0 e1 e
    | CtxStore1 e2 e3 => Store e e2 e3
    | CtxStore2 e1 e3 => Store e1 e e3
    | CtxStore3 e1 e2 => Store e1 e2 e
    end.

Definition ctxi_split c :=
  match c with
  | CtxPair1 e2 => (HeadPair, [e2])
  | CtxPair2 e1 => (HeadPair, [e1])
  | CtxPairDet1 e2 => (HeadPairDet, [e2])
  | CtxPairDet2 e1 => (HeadPairDet, [e1])
  | CtxLet1 e2 => (HeadLet, [e2])
  | CtxLet2 e1 => (HeadLet, [e1])
  | CtxMatch0 e1 e2 => (HeadMatch, [e1 ; e2])
  | CtxMatch1 e0 e2 => (HeadMatch, [e0 ; e2])
  | CtxMatch2 e0 e1 => (HeadMatch, [e0 ; e1])
  | CtxStore1 e2 e3 => (HeadStore, [e2 ; e3])
  | CtxStore2 e1 e3 => (HeadStore, [e1 ; e3])
  | CtxStore3 e1 e2 => (HeadStore, [e1 ; e2])
  end.

Global Instance ctxi_well_formed : WellFormed ctxi :=
  λ c,
    let '(hd, es) := ctxi_split c in
    well_formed hd ∧ Forall well_formed es.

(* ---------- ctx ---------- *)

Notation ctx := (list ctxi).

Global Instance ctx_well_formed : WellFormed ctx :=
  Forall well_formed.
