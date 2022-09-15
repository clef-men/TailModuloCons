From tmc.common Require Import
  prelude.

Class WellFormed X :=
  well_formed : X → Prop.
