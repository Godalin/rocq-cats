From Cats Require Import
  Cat.Diagram.PrismReconstruction
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Reconstruction with Independent Hom and Equality Sizes

    Source and target have opposite carrier/equality size profiles. Check
    reconstruction, boundary comparison and unique extension without
    identifying these levels or assuming transformations invertible. *)

(** * Hom 与相等大小独立的重建

    源与目标使用相反的载体／相等大小配置。检查重建、边界比较及唯一延拓，
    不识别这些层级，也不假设自然变换可逆。 *)

Section Levels.
Universes e h o l.
Constraint e < h.
Constraint h < o.
Constraint o < l.

Context (C : Cat@{o h e l l}) (D : Cat@{h e o l l})
    (K : Functor (C ×C [Ord 1]) D)
    (F G : Functor C D) (α : F ⇒ G)
    (a : F ⇒ π1F K fin_first)
    (b : G ⇒ π1F K (fin_next fin_first))
    (H : (b ∘Nv α) ≈N (PrismTransformationN K ∘Nv a)).

(** Rebuilding an arbitrary prism retains independent native sizes. *)

(** 重建任意棱柱保留独立的原生大小。 *)

Definition independent_reconstruction
  : NaturalPrismF (PrismTransformationN K) ≅N K
  := prism_reconstruction_iso K.

(** The transformation round trip also works in these size profiles. *)

(** 自然变换的往返律也适用于这些大小配置。 *)

Definition independent_transformation_roundtrip
  : (NaturalPrismBoundaryN α (fin_next fin_first) ∘Nv
      PrismTransformationN (NaturalPrismF α)) ≈N
      (α ∘Nv NaturalPrismBoundaryN α fin_first)
  := natural_prism_transformation_β α.

(** The universal property uses Type-valued equality at its own level. *)

(** 泛性质使用处于自身层级的 Type 值相等。 *)

Definition independent_unique_comparison
  : is_unique (R := @NatEq _ _ _ _)
      (is_prism_comparison K α a b) (PrismComparisonN K α a b H)
  := prism_comparison_universal K α a b H.

End Levels.
