From Cats Require Import
  Cat.Diagram.PrismReconstruction
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Reconstruction with Independent Hom and Equality Sizes

    Source and target have opposite carrier/equality size profiles. Check
    reconstruction, boundary comparison and unique extension without
    identifying these levels or assuming transformations invertible. *)

Section Levels.
Universes e h o l.
Constraint e < h.
Constraint h < o.
Constraint o < l.

Context (C : Cat@{o h e l l}) (D : Cat@{h e o l l})
    (K : Fct (C ×C [Ord 1]) D)
    (F G : Fct C D) (α : F ⇒ G)
    (a : F ⇒ AtRF K fin_first)
    (b : G ⇒ AtRF K (fin_next fin_first))
    (H : (b ∘Nv α) ≈N (PrismTransformationN K ∘Nv a)).

(** Rebuilding an arbitrary prism retains independent native sizes. *)

Definition independent_reconstruction
  : NatPrismF (PrismTransformationN K) ≅N K
  := prism_reconstruction_iso K.

(** The transformation round trip also works in these size profiles. *)

Definition independent_transformation_roundtrip
  : (NatPrismBoundaryN α (fin_next fin_first) ∘Nv
      PrismTransformationN (NatPrismF α)) ≈N
      (α ∘Nv NatPrismBoundaryN α fin_first)
  := natural_prism_transformation_β α.

(** The universal property uses Type-valued equality at its own level. *)

Definition independent_unique_comparison
  : is_unique (R := @NatEq _ _ _ _)
      (is_prism_comparison K α a b) (PrismComparisonN K α a b H)
  := prism_comparison_universal K α a b H.

End Levels.
