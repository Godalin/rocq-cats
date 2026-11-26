From Cats Require Import
  Cat.Core
  Instance.Bool.CocycleSphereCylinder.

Import Cats.Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Cylinder Constructed from a Tetrahedron Generator

    The class equality below is a retained tetrahedron step, not native
    reflexivity. The resulting cylinder must still compute without
    normalizing equality witnesses or losing its spatial/time coordinates. *)

Fail Definition unchosen_coefficient_group
  : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid)
  := _.

Fail Definition unchosen_class_group
  : HasMagma BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.


(** Freely label a retained representative at the model's native sizes. *)

Definition label_sphere (a : bool)
  : BoolCocycleSphereClassS
  := (cocycle_two_sphere_class_resp (M := BoolS_Monoid)) a.

(** An actual elementary tetrahedron gives the class witness supplied to
    the reverse cylinder comparison. *)

Definition label_cylinder (a : bool)
  : TwoSphereCylinderHomotopy BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      (label_sphere a) (label_sphere a)
  := CocycleTwoSphereCylinder (label_sphere a) (label_sphere a)
      (two_sphere_class_step BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
        (CocycleTwoSphereHomotopy (label_sphere a) (label_sphere a) eq_refl)).

(** Every time operator computes the same triangle coefficient. *)

Example cylinder_value_computes (a : bool) (t : (@Hom Δ) 2 1%nat)
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (two_sphere_cylinder_eval BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
        (label_cylinder a) id t) = a.
Proof. reflexivity. Defined.

(** Read a face of one of the three actual prism tetrahedra. *)

Definition prism_face_value (a : bool) (i : Ordinal 2) (j : Ordinal 3)
  : bool
  := (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (d[BoolCocycleModel; 2; j] (two_sphere_prism (label_cylinder a) i)).

(** All twelve coefficients compute with the expected staircase orientation.
    This checks the actual maps, not only the proved face equations. *)

Example prism_faces_compute (a : bool)
  : ((prism_face_value a fin_first fin_first,
      prism_face_value a fin_first fin_first⁺,
      prism_face_value a fin_first fin_first⁺⁺,
      prism_face_value a fin_first fin_first⁺⁺⁺),
     (prism_face_value a fin_first⁺ fin_first,
      prism_face_value a fin_first⁺ fin_first⁺,
      prism_face_value a fin_first⁺ fin_first⁺⁺,
      prism_face_value a fin_first⁺ fin_first⁺⁺⁺),
     (prism_face_value a fin_first⁺⁺ fin_first,
      prism_face_value a fin_first⁺⁺ fin_first⁺,
      prism_face_value a fin_first⁺⁺ fin_first⁺⁺,
      prism_face_value a fin_first⁺⁺ fin_first⁺⁺⁺)) =
      ((a, a, false, false), (false, a, a, false), (false, false, a, a)).
Proof. reflexivity. Defined.
