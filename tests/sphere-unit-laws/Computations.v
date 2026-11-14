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

(** * 实际单位与逆候选的计算

    检查退化单位四面体及已集成逆候选填充。类乘法仍计算实际 Kan 填充的输出；
    在显式选定原群上消费四条类定律，不假设结合律。 *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Full Kan enabling does not select either algebraic structure. *)

(** 启用完整 Kan 不会选择任何一个代数结构。 *)

Fail Definition unchosen_magma
  : Magma BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_group
  : Group BoolCocycleSphereClassS
  := _.

(** Explicit multiplication and independent inverse-candidate choices. *)

(** 显式乘法及独立逆候选选择。 *)

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
  : Magma BoolCocycleSphereClassS
  := TwoSphereClassMagma BoolCocycleModel (two_cocycle_simplex_unit 0)
      three_choice.

(** Retain both actual inverse candidates and their tetrahedra. *)

(** 保留两个实际逆候选及其四面体。 *)

Definition left_candidate
  := @SphereKanLeftInverse BoolCocycleModel (two_cocycle_simplex_unit 0)
      left_choice (cocycle_two_sphere_resp true).

Definition right_candidate
  := @SphereKanRightInverse BoolCocycleModel (two_cocycle_simplex_unit 0)
      right_choice (cocycle_two_sphere_resp true).

(** Read every triangular face in its fixed order. *)

(** 按固定次序读取全部三角形面。 *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example tetrahedra_compute
  : (face_values (SphereLeftUnitComposite BoolCocycleModel
        (two_cocycle_simplex_unit 0) (cocycle_two_sphere_resp true)).1,
     face_values (SphereRightUnitComposite BoolCocycleModel
        (two_cocycle_simplex_unit 0) (cocycle_two_sphere_resp true)).1,
     face_values left_candidate.2.1, face_values right_candidate.2.1)
      = ((false, true, true, false), (false, false, true, true),
         (false, true, false, true), (false, true, false, true)).
Proof. vm_compute. reflexivity. Defined.

(** Compute through the selected magma, retaining the Kan multiplication. *)

(** 通过选定原群计算，保留 Kan 乘法。 *)

Definition product_value (x y : BoolCocycleSphereClassS)
  : bool
  := cocycle_two_sphere_class_value_resp (@magma_mul _ class_magma x y).

Example products_compute
  : (product_value (two_sphere_base BoolCocycleModel
        (two_cocycle_simplex_unit 0)) (cocycle_two_sphere_resp true),
     product_value (cocycle_two_sphere_resp true)
       (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)),
     product_value left_candidate.1 (cocycle_two_sphere_resp true),
     product_value (cocycle_two_sphere_resp true) right_candidate.1)
      = (true, true, false, false).
Proof. vm_compute. reflexivity. Defined.

(** The generic class laws apply to the very same chosen multiplication. *)

(** 一般类定律适用于完全相同的选定乘法。 *)

Example left_unit_client
  : @magma_mul _ class_magma (two_sphere_base BoolCocycleModel
      (two_cocycle_simplex_unit 0)) (cocycle_two_sphere_resp true) ≈S
      (cocycle_two_sphere_resp true : BoolCocycleSphereClassS).
Proof.
  exact (two_sphere_kan_mul_unit_l BoolCocycleModel
    (two_cocycle_simplex_unit 0) three_choice (cocycle_two_sphere_resp true)).
Defined.

Example right_unit_client
  : @magma_mul _ class_magma (cocycle_two_sphere_resp true)
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)) ≈S
      (cocycle_two_sphere_resp true : BoolCocycleSphereClassS).
Proof.
  exact (two_sphere_kan_mul_unit_r BoolCocycleModel
    (two_cocycle_simplex_unit 0) three_choice (cocycle_two_sphere_resp true)).
Defined.

Example left_inverse_client
  : @magma_mul _ class_magma left_candidate.1
      (cocycle_two_sphere_resp true) ≈S
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)
        : BoolCocycleSphereClassS).
Proof.
  exact (two_sphere_kan_mul_inverse_l BoolCocycleModel
    (two_cocycle_simplex_unit 0) three_choice left_choice
    (cocycle_two_sphere_resp true)).
Defined.

Example right_inverse_client
  : @magma_mul _ class_magma (cocycle_two_sphere_resp true)
      right_candidate.1 ≈S
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)
        : BoolCocycleSphereClassS).
Proof.
  exact (two_sphere_kan_mul_inverse_r BoolCocycleModel
    (two_cocycle_simplex_unit 0) three_choice right_choice
    (cocycle_two_sphere_resp true)).
Defined.
