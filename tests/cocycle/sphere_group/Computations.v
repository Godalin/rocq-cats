From Cats Require Import
  Instance.Bool.CocycleSphereGroup.

Local Open Scope ordinal_scope.
Local Open Scope algebra_scope.

(** * Explicit Selection and Geometric Computation

    Importing the new group construction must not enable either the
    coefficient group, the class monoid/group, or the Kan structure.
    Once enabled locally, multiplication must compute xor and an actual
    retained composition tetrahedron must compute all four face labels. *)

Fail Definition unchosen_coefficient_group
  : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid)
  := _.

Fail Definition unchosen_class_magma
  : HasMagma BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolCocycleModel_HasKanFillers.

(** The bundled multiplication computes xor on any two Boolean labels. *)

Example class_product_computes (a b : bool)
  : (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
      ((@cocycle_two_sphere_class_resp BoolS_Monoid a : BoolCocycleSphereClassS_Group) ⋅
        @cocycle_two_sphere_class_resp BoolS_Monoid b) = xorb a b.
Proof. reflexivity. Defined.

(** The bundled inverse is computational, with no opaque inverse choice. *)

Example class_inverse_computes (a : bool)
  : (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
      ((@cocycle_two_sphere_class_resp BoolS_Monoid a : BoolCocycleSphereClassS_Group)⁻¹) = a.
Proof. reflexivity. Defined.

(** The actual constant sphere is the bundled unit. *)

Example class_unit_computes
  : (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) (1 : BoolCocycleSphereClassS_Group) = false.
Proof. reflexivity. Defined.

(** The square tetrahedron retains one constant face, the product face,
    and both nonzero input faces in the expected orientation. *)

Example square_faces_compute
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid)
        (d[BoolCocycleModel; 2; fin_first] BoolCocycleSphereSquare.1),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺] BoolCocycleSphereSquare.1),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺] BoolCocycleSphereSquare.1),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] BoolCocycleSphereSquare.1)) =
      (false, true, false, true).
Proof. reflexivity. Defined.

(** Apply the general independence theorem to the previously constructed
    full Kan choice, not just to our explicit tetrahedron. *)

Example chosen_Kan_product_class
  : (cocycle_two_sphere_face
      (horn_fill (cocycle_two_sphere_horn
        bool_cocycle_sphere bool_cocycle_sphere)).1
      : BoolCocycleSphereClassS_Group) ≈S 1.
Proof.
  transitivity (cocycle_two_sphere_mul (M := BoolS_Monoid) bool_cocycle_sphere bool_cocycle_sphere).
  - apply cocycle_two_sphere_horn_unique. apply (horn_fill _).2.
  - exact bool_cocycle_sphere_square.
Defined.
