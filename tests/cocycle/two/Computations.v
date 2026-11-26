From Cats Require Import
  Instance.Bool.Cocycle
  Cat.Shape.Ordinal.

(** * A Nonzero Triangle Label

    In the ordered triangle [Ord 2], mark only the long edge 0 to 2.
    Its coboundary labels the triangle by [true]. Triangles with identity
    short edges still have label [false]. These tests inspect computations,
    rather than proving general equations already in the theory modules. *)

(** Importing the example must not implicitly select its coefficient monoid. *)

Fail Definition unchosen_boolean_monoid
  : @HasUnit BoolS_Semigroup (Semigroup_hasMagma BoolS_Semigroup)
  := ltac:(typeclasses eauto).

Example triangle_label_computes
  : BoolTriangleCocycle⟦ordinal_step (@fin_first 1),
      ordinal_step (fin_next (@fin_first 0))⟧₂ = true.
Proof. reflexivity. Qed.

Example identity_triangle_computes
  : BoolTriangleCocycle⟦@Cat.Core.id [Ord 2] fin_first,
      ordinal_step (@fin_first 1)⟧₂ = false.
Proof. reflexivity. Qed.

Example pulled_back_label_computes
  : (TwoCocyclePullback IdF BoolTriangleCocycle)⟦
      ordinal_step (@fin_first 1),
      ordinal_step (fin_next (@fin_first 0))⟧₂ = true.
Proof. reflexivity. Qed.

Example constant_label_computes
  : (@UnitTwoCocycle [Ord 2] BoolS_Monoid)⟦
      ordinal_step (@fin_first 1),
      ordinal_step (fin_next (@fin_first 0))⟧₂ = false.
Proof. reflexivity. Qed.
