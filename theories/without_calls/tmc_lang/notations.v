From tmc.common Require Import
  prelude.
From tmc.without_calls Require Import
  language.lang.
From tmc.without_calls.tmc_lang Require Export
  syntax.

Coercion Loc : loc >-> val.
Coercion Index : index >-> val.
Coercion Val : val >-> expr.

(* ---------- index ---------- *)

Declare Scope index_scope.
Delimit Scope index_scope with index.
Bind Scope index_scope with index.

Notation "𝟙" := one : index_scope.
Notation "𝟚" := two : index_scope.

(* ---------- val ---------- *)

Notation "()" := Unit : val_scope.

(* ---------- expr ---------- *)

Notation "& x" := (Var x%nat)
( at level 8,
  format "& x"
) : expr_scope.

Notation "# v" := (Val v%V%index)
( at level 8,
  format "# v"
).

Notation "'fail'" := Fail
: expr_scope.

Notation "( e1 , e2 , .. , en )" := (Pair .. (Pair e1%E e2%E) .. en%E)
: expr_scope.

Notation "⟨ e1 , e2 ⟩" := (PairDet e1%E e2%E)
( format "'[hv' ⟨ e1 ,  e2 ⟩ ']'"
) : expr_scope.

Notation "'let:' e1 'in' e2" := (Let e1%E e2%E)
( at level 200,
  e1, e2 at level 200,
  format "'[v' 'let:'  '[' e1 ']'  'in' '/' e2 ']'"
) : expr_scope.

Notation Seq e1 e2 := (Let e1 e2.[ren (+1)]) (only parsing).
Notation ECtxSeq e2 := (ECtxLet e2.[ren (+1)]) (only parsing).
Notation "e1 ;; e2" := (Seq e1%E e2%E)
( at level 100,
  e2 at level 200,
  format "'[v' '[hv' '[' e1 ']'  ;; ']' '/' e2 ']'"
) : expr_scope.

Notation "'match:' e0 'with' () => e1 | '_' => e2 'end'" := (Match e0%E e1%E e2%E)
( e0, e1, e2 at level 200,
  format "'[hv' 'match:'  e0  'with'  '/  ' '[' ()  =>  '/    ' e1 ']'  '/' '[' |  '_'  =>  '/    ' e2 ']'  '/' 'end' ']'"
) : expr_scope.

Notation "e1 .# e2 '<-' e3" := (Store e1%E e2%E e3%E)
( at level 80,
  e2 at level 200
) : expr_scope.
