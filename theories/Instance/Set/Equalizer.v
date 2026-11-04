From Cats Require Import
  Cat.Core
  Cat.Equalizer
  Cat.Limit.Finite
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Pullback.

(** * Equalizers from the Chosen Setoid Pullbacks *)

(** * 从选定广集拉回得到等化子 *)

(** Reuse the diagonal pullback construction. Its carrier retains equality
    witnesses, hence the original model requires [p ≤ u]. *)

(** 复用对角拉回构造；载体保留相等见证，因而原模型要求 [p ≤ u]。 *)

Definition SetCat_HasEqualizer@{u p +}
  : HasEqualizer (SetCat@{u p _ _ _ _ _})
  := @ProductPullbackEqualizer SetCat SetCat_HasProduct SetCat_HasPullback.
