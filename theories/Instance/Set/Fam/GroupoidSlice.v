From Cats Require Import
  Cat.Core
  Cat.CatCat
  Cat.Functor.Core
  Cat.Natural
  Cat.Slice.Core
  Instance.Set.Core
  Instance.Set.Groupoid
  Instance.Set.Fam.Groupoid
  Instance.Set.Fam.Slice.

(** * Equality-Groupoid Actions and Slices

    Compose the family-action equivalence with the existing family-slice
    equivalence. This specialization retains the latter's size condition:
    base equality witnesses fit in the common carrier universe, [p <= u]. *)

(** * 相等群胚作用与切片

    将族与作用的等价同已有的族与切片等价复合。此特化保留后者的大小条件：
    基底相等见证须容纳于共同载体宇宙，即 [p <= u]。 *)

Definition action_slice_equiv@{u p +} (X : SetC@{u p})
  : FctCat (EqGpd X) SetCat ≃C (SetCat /C X)
  := iso_trans (iso_symm (fam_action_equiv X)) (fam_slice_equiv X).
