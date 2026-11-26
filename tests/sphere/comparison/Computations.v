From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereKanComparison
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Comparing Generic and Coefficient-Built Tetrahedra

    One composite is selected by the actual Boolean Kan filler; the other
    is built directly by the existing cocycle product construction. Their
    comparison uses the generic four-horn filler, not coefficient equality
    as a replacement for a homotopy. *)

Fail Definition unchosen_group
  : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid)
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Fail Definition unchosen_four_horn
  : HasHornFillers BoolCocycleModel 4 fin_first⁺⁺
  := _.

Local Existing Instance BoolCocycleModel_HasKanFillers.

(** The generic selected composite, retaining its tetrahedron. *)

Definition selected (a b : bool)
  : ∃ z : TwoSphereS BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0),
      TwoSphereComposite BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) a) (cocycle_two_sphere_resp (M := BoolS_Monoid) b) z
  := SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) a) (cocycle_two_sphere_resp (M := BoolS_Monoid) b).

(** The direct product composite uses the existing coefficient construction. *)

Definition direct (a b : bool)
  : TwoSphereComposite BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) a) (cocycle_two_sphere_resp (M := BoolS_Monoid) b)
      (cocycle_two_sphere_mul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) b))
  := (CocycleTwoSphereMul (M := BoolS_Monoid)) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) b).

(** Retain the elementary comparison homotopy itself. *)

Definition comparison (a b : bool)
  : TwoSphereHomotopy BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      (selected a b).1
      (cocycle_two_sphere_mul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) b))
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (selected a b).2 (direct a b).

(** Read the four actual triangle faces of a tetrahedron. *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (M := BoolS_Monoid) (d[BoolCocycleModel; 2; fin_first] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

(** All four products give homotopies with two constant faces and the two
    output triangles, in the asserted orientation. *)

Example comparison_faces_compute
  : (face_values (comparison false false).1,
     face_values (comparison false true).1,
     face_values (comparison true false).1,
     face_values (comparison true true).1)
      = ((false, false, false, false), (false, false, true, true),
         (false, false, true, true), (false, false, false, false)).
Proof. vm_compute. reflexivity. Defined.

(** Read the actual selected four-simplex before taking its omitted face. *)

Definition comparison_volume (a b : bool)
  : BoolCocycleModel 4
  := (horn_fill (SphereCompositeComparisonHornN BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (selected a b).2 (direct a b))).1.

(** All five tetrahedra compute, including the formerly omitted homotopy. *)

Example volume_faces_compute
  : (face_values (d[BoolCocycleModel; 3; fin_first]
        (comparison_volume true true)),
     face_values (d[BoolCocycleModel; 3; fin_first⁺]
        (comparison_volume true true)),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺]
        (comparison_volume true true)),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺⁺]
        (comparison_volume true true)),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺⁺⁺]
        (comparison_volume true true)))
      = ((false, false, false, false), (false, false, true, true),
         (false, false, false, false), (false, true, false, true),
         (false, true, false, true)).
Proof. vm_compute. reflexivity. Defined.

(** The new generated class equation is consumed by the existing coefficient
    evaluator; no axiom about the two filler records is available. *)

Example comparison_class_evaluates (a b : bool)
  : (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) (selected a b).1 ≈S
      (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
        (cocycle_two_sphere_mul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
          (cocycle_two_sphere_resp (M := BoolS_Monoid) b)).
Proof.
  apply func_proper. exact (two_sphere_composite_output_eq BoolCocycleModel
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (selected a b).2 (direct a b)).
Defined.
