From simuliris.common Require Import
  prelude.
From simuliris.without_calls.tmc Require Export
  lang.syntax.

(* ---------- index ---------- *)

Declare Scope index_scope.
Delimit Scope index_scope with index.
Bind Scope index_scope with index.

Notation "𝟙" := one.
Notation "𝟚" := two.

(* ---------- val ---------- *)

Coercion Block : block >-> val.
Coercion Index : index >-> val.

Declare Scope val_scope.
Delimit Scope val_scope with V.
Bind Scope val_scope with val.

Notation "()" := Unit
: val_scope.

(* ---------- expr ---------- *)

Coercion Val : val >-> expr.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.

Notation "& x" := (Var x%nat%stdpp)
( at level 8,
  format "& x"
).

Notation "# v" := (Val v%index%V%stdpp)
( at level 8,
  format "# v"
).

Notation "'fail'" := Fail
: expr_scope.

Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1%V%E e2%V%E) .. en%V%E)
: expr_scope.

Notation "⟨ e1 , e2 ⟩" := (PairDet e1%V%E e2%V%E)
( format "'[hv' ⟨ e1 ,  e2 ⟩ ']'"
) : expr_scope.

Notation "'let:' e1 'in' e2" := (Let e1%V%E e2%V%E)
( at level 200,
  e1, e2 at level 200,
  format "'[v' 'let:'  '[' e1 ']'  'in' '/' e2 ']'"
) : expr_scope.

Notation Seq e1 e2 := (Let e1 e2.[ren (+1)]) (only parsing).
Notation ECtxSeq e2 := (EctxLet e2.[ren (+1)]) (only parsing).
Notation "e1 ;; e2" := (Seq e1%V%E e2%V%E)
( at level 100,
  e2 at level 200,
  format "'[v' '[hv' '[' e1 ']'  ;; ']' '/' e2 ']'"
) : expr_scope.

Notation "'match:' e0 'with' () => e1 | '_' => e2 'end'" := (Match e0%V%E e1%V%E e2%V%E)
( e0, e1, e2 at level 200,
  format "'[hv' 'match:'  e0  'with'  '/  ' '[' ()  =>  '/    ' e1 ']'  '/' '[' |  '_'  =>  '/    ' e2 ']'  '/' 'end' ']'"
) : expr_scope.

Notation "e1 .# e2 '<-' e3" := (Store e1%V%E e2%V%E e3%V%E)
( at level 80,
  e2 at level 200
) : expr_scope.
