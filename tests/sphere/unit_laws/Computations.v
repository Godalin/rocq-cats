From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereUnit
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Unit and Candidate-Inverse Computations

    Inspect the degenerate unit tetrahedra and the already integrated
    inverse-candidate fillers. Class multiplication still computes an
    actual Kan filler output; the four class laws are consumed on the
    explicitly selected magma without assuming associativity. *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Full Kan enabling does not select either algebraic structure. *)

Fail Definition unchosen_magma
  : HasMagma BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_group
  : HasMagma BoolCocycleSphereClassS
  := _.

(** Explicit multiplication and independent inverse-candidate choices. *)

Definition three_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Definition left_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺⁺
  := _.

Definition right_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺
  := _.

Definition class_magma
  : Magma
  := TwoSphereClassMagma BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      three_choice.

(** Retain both actual inverse candidates and their tetrahedra. *)

Definition left_candidate
  := @SphereKanLeftInverse BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      left_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

Definition right_candidate
  := @SphereKanRightInverse BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      right_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

(** Read every triangular face in its fixed order. *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (M := BoolS_Monoid) (d[BoolCocycleModel; 2; fin_first] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example tetrahedra_compute
  : (face_values (SphereLeftUnitComposite BoolCocycleModel
        (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).1,
     face_values (SphereRightUnitComposite BoolCocycleModel
        (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).1,
     face_values left_candidate.2.1, face_values right_candidate.2.1)
      = ((false, true, true, false), (false, false, true, true),
         (false, true, false, true), (false, true, false, true)).
Proof. vm_compute. reflexivity. Defined.

(** Compute through the selected magma, retaining the Kan multiplication. *)

Definition product_value (x y : BoolCocycleSphereClassS)
  : bool
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) (@mul _ (hasMagma class_magma) x y).

Example products_compute
  : (product_value (two_sphere_base BoolCocycleModel
        (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)) (cocycle_two_sphere_resp (M := BoolS_Monoid) true),
     product_value (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
       (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)),
     product_value left_candidate.1 (cocycle_two_sphere_resp (M := BoolS_Monoid) true),
     product_value (cocycle_two_sphere_resp (M := BoolS_Monoid) true) right_candidate.1)
      = (true, true, false, false).
Proof. vm_compute. reflexivity. Defined.

(** The generic class laws apply to the very same chosen multiplication. *)

Example left_unit_client
  : @mul _ (hasMagma class_magma) (two_sphere_base BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)) (cocycle_two_sphere_resp (M := BoolS_Monoid) true) ≈S
      (cocycle_two_sphere_resp (M := BoolS_Monoid) true : BoolCocycleSphereClassS).
Proof.
  exact (two_sphere_kan_mul_unit_l BoolCocycleModel
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).
Defined.

Example right_unit_client
  : @mul _ (hasMagma class_magma) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)) ≈S
      (cocycle_two_sphere_resp (M := BoolS_Monoid) true : BoolCocycleSphereClassS).
Proof.
  exact (two_sphere_kan_mul_unit_r BoolCocycleModel
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).
Defined.

Example left_inverse_client
  : @mul _ (hasMagma class_magma) left_candidate.1
      (cocycle_two_sphere_resp (M := BoolS_Monoid) true) ≈S
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
        : BoolCocycleSphereClassS).
Proof.
  exact (two_sphere_kan_mul_inverse_l BoolCocycleModel
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice left_choice
    (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).
Defined.

Example right_inverse_client
  : @mul _ (hasMagma class_magma) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
      right_candidate.1 ≈S
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
        : BoolCocycleSphereClassS).
Proof.
  exact (two_sphere_kan_mul_inverse_r BoolCocycleModel
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice right_choice
    (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).
Defined.
