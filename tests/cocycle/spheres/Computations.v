From Cats Require Import
  Algebra.Group.Cocycle
  Instance.Bool.CocycleSphere.

Local Open Scope ordinal_scope.

(** * Retained Representatives and Tetrahedron Computation

    Importing the comparison does not select a Boolean coefficient group
    or Kan structure. The selected sphere representatives and actual
    elementary homotopy tetrahedron nevertheless remain transparent. *)

Fail Definition unchosen_boolean_group
  : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid)
  := _.

Fail Definition unchosen_boolean_Kan
  : HasKanFillers BoolCocycleModel
  := _.

(** Constructing and then decoding a class computes its original label. *)

Example class_label_computes (a : bool)
  : (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
      (@cocycle_two_sphere_class_resp BoolS_Monoid a
        : BoolCocycleSphereClassS) = a.
Proof. reflexivity. Defined.

(** Decoding the distinguished sphere computes the Boolean unit. *)

Example base_label_computes
  : (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)) = false.
Proof. reflexivity. Defined.

(** Retain an actual homotopy between two copies of the true sphere. *)

Definition true_sphere_homotopy
  : TwoSphereHomotopy BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      bool_cocycle_sphere bool_cocycle_sphere
  := CocycleTwoSphereHomotopy
      bool_cocycle_sphere bool_cocycle_sphere eq_refl.

(** Both constant faces and both nonconstant endpoint faces compute from
    the retained tetrahedron, rather than just from its law witnesses. *)

Example homotopy_faces_compute
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid)
        (d[BoolCocycleModel; 2; fin_first] true_sphere_homotopy.1),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺] true_sphere_homotopy.1),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺] true_sphere_homotopy.1),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] true_sphere_homotopy.1)) =
      (false, false, true, true).
Proof. reflexivity. Defined.
