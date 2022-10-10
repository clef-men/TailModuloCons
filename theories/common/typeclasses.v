From simuliris.common Require Import
  prelude.

Class SqSubset X :=
  sqsubset : relation X.
Infix "⊏" := sqsubset
( at level 70
) : stdpp_scope.
Infix "⊏@{ X }" := (@sqsubset X _)
( at level 70,
  only parsing
) : stdpp_scope.
Notation "(⊏)" := sqsubset
( only parsing
) : stdpp_scope.
Notation "(⊏@{ X } )" := (@sqsubset X _)
( only parsing
) : stdpp_scope.
Notation "( x ⊏.)" := (sqsubset x)
( only parsing
) : stdpp_scope.
Notation "(.⊏ y )" := (λ x, sqsubset x y)
( only parsing
) : stdpp_scope.

Class Similar X Y :=
  similar : X → Y → Prop.
Infix "≈" := similar
( at level 70,
  no associativity
) : stdpp_scope.
Infix "{ X }@≈@{ Y }" := (@similar X Y _)
( at level 70,
  no associativity,
  only parsing
) : stdpp_scope.
Notation "(≈)" := similar
( only parsing
) : stdpp_scope.
Notation "({ X }@≈@{ Y } )" := (@similar X Y _)
( only parsing
) : stdpp_scope.
Notation "( x ≈.)" := (similar x)
( only parsing
) : stdpp_scope.
Notation "(.≈ y )" := (λ x, similar x y)
( only parsing
) : stdpp_scope.

Class Refines X Y :=
  refines : X → Y → Prop.
Infix "⊴" := refines
( at level 70,
  no associativity
) : stdpp_scope.
Infix "{ X }@⊴@{ Y }" := (@refines X Y _)
( at level 70,
  no associativity,
  only parsing
) : stdpp_scope.
Notation "(⊴)" := refines
( only parsing
) : stdpp_scope.
Notation "({ X }@⊴@{ Y } )" := (@refines X Y _)
( only parsing
) : stdpp_scope.
Notation "( x ⊴.)" := (refines x)
( only parsing
) : stdpp_scope.
Notation "(.⊴ y )" := (λ x, refines x y)
( only parsing
) : stdpp_scope.

Class WellFormed X :=
  well_formed : X → Prop.

Class Closed X :=
  closed : X → Prop.

Class Fill ctx expr :=
  fill : ctx → expr → expr.
Global Arguments fill {_ _ _} _ _ : assert.
Notation "C @@ e" := (fill C e)
( at level 20
) : stdpp_scope.
Notation "(@@)" := fill
( only parsing
) : stdpp_scope.
Notation "( C @@.)" := (fill C)
( only parsing
) : stdpp_scope.
Notation "(.@@ e )" := (λ C, fill C e)
( only parsing
) : stdpp_scope.
