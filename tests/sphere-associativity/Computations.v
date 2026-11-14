From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereAssociativity
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Rebracketing and Class Associativity

    Glue coefficient-built composite tetrahedra, fill their actual
    four-horn with the integrated Kan model, and inspect all five faces.
    Then compute both bracketings of the actual selected multiplication
    and consume the general law on the previously selected class magma. *)

(** * 实际重括号与类结合律

    粘合由系数构造的合成四面体，用已集成 Kan 模型填充其实际四维 horn，并
    检查全部五个面。随后计算实际选定乘法的两种括号方式，在此前选定类原群上
    消费一般结合律。 *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Proving associativity does not register stronger selected structures. *)

(** 证明结合律不会注册更强的选定结构。 *)

Fail Definition unchosen_semigroup
  : Semigroup BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_group
  : Group BoolCocycleSphereClassS
  := _.

(** Three true-labelled inputs have false-labelled intermediate products. *)

(** 三个 true 标签输入具有 false 标签中间乘积。 *)

Definition first_composite
  := CocycleTwoSphereMul (cocycle_two_sphere_resp true)
      (cocycle_two_sphere_resp true).

Definition second_composite
  := CocycleTwoSphereMul (cocycle_two_sphere_resp true)
      (cocycle_two_sphere_resp true).

Definition left_composite
  := CocycleTwoSphereMul
      (cocycle_two_sphere_mul (cocycle_two_sphere_resp true)
        (cocycle_two_sphere_resp true)) (cocycle_two_sphere_resp true).

(** Retain the actual horn and its selected four-simplex filler. *)

(** 保留实际 horn 及其选定四维单形填充。 *)

Definition assoc_horn
  := SphereAssociativityHornN BoolCocycleModel (two_cocycle_simplex_unit 0)
      first_composite second_composite left_composite.

Definition assoc_filler
  := horn_fill assoc_horn.

(** Exercise both the supplied-filler and minimal chosen interfaces. *)

(** 同时消费给定填充及最小选定接口。 *)

Definition given_rebracketing
  := SphereCompositeReassociateOfFiller BoolCocycleModel
      (two_cocycle_simplex_unit 0) first_composite second_composite
      left_composite assoc_filler.1 assoc_filler.2.

Definition chosen_rebracketing
  := SphereCompositeReassociate BoolCocycleModel (two_cocycle_simplex_unit 0)
      first_composite second_composite left_composite.

(** Inspect the four triangular faces of a tetrahedron. *)

(** 检查四面体的四个三角形面。 *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example actual_horn_computes
  : (face_values (d[BoolCocycleModel; 3; fin_first] assoc_filler.1),
     face_values (d[BoolCocycleModel; 3; fin_first⁺] assoc_filler.1),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺] assoc_filler.1),
     face_values given_rebracketing.1,
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺⁺⁺] assoc_filler.1),
     face_values chosen_rebracketing.1)
      = ((false, false, false, false), (false, true, false, true),
         (false, true, true, false), (false, false, true, true),
         (false, true, false, true), (false, false, true, true)).
Proof. vm_compute. reflexivity. Defined.

(** Keep the actual selected multiplication for both bracketings. *)

(** 两种括号方式都保留实际选定乘法。 *)

Definition three_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Definition bracket_values (a b c : bool)
  : bool * bool
  := (cocycle_two_sphere_class_value_resp
        (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit 0)
          three_choice
          (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit 0)
            three_choice (cocycle_two_sphere_resp a)
            (cocycle_two_sphere_resp b))
          (cocycle_two_sphere_resp c)),
      cocycle_two_sphere_class_value_resp
        (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit 0)
          three_choice (cocycle_two_sphere_resp a)
          (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit 0)
            three_choice (cocycle_two_sphere_resp b) (cocycle_two_sphere_resp c)))).

Example all_bracketings_compute
  : (bracket_values false false false, bracket_values false false true,
     bracket_values false true false, bracket_values false true true,
     bracket_values true false false, bracket_values true false true,
     bracket_values true true false, bracket_values true true true)
      = ((false, false), (true, true), (true, true), (false, false),
         (true, true), (false, false), (false, false), (true, true)).
Proof. vm_compute. reflexivity. Defined.

(** Compare unrelated supplied composites through the actual horn proof. *)

(** 经实际 horn 证明比较无关构造的给定合成。 *)

Example supplied_outputs_associate
  : (cocycle_two_sphere_mul
        (cocycle_two_sphere_mul (cocycle_two_sphere_resp true)
          (cocycle_two_sphere_resp true)) (cocycle_two_sphere_resp true)
      : BoolCocycleSphereClassS) ≈S
      cocycle_two_sphere_mul (cocycle_two_sphere_resp true)
        (cocycle_two_sphere_mul (cocycle_two_sphere_resp true)
          (cocycle_two_sphere_resp true)).
Proof.
  exact (two_sphere_composite_assoc BoolCocycleModel
    (two_cocycle_simplex_unit 0) first_composite second_composite left_composite
    (CocycleTwoSphereMul (cocycle_two_sphere_resp true)
      (cocycle_two_sphere_mul (cocycle_two_sphere_resp true)
        (cocycle_two_sphere_resp true)))).
Defined.

(** Use exactly the existing selected magma, without choosing a semigroup. *)

(** 使用完全相同的既有选定原群，不选择半群。 *)

Definition class_magma
  : Magma BoolCocycleSphereClassS
  := TwoSphereClassMagma BoolCocycleModel (two_cocycle_simplex_unit 0)
      three_choice.

Example magma_associates (x y z : BoolCocycleSphereClassS)
  : @magma_mul _ class_magma (@magma_mul _ class_magma x y) z ≈S
      @magma_mul _ class_magma x (@magma_mul _ class_magma y z).
Proof.
  exact (two_sphere_kan_mul_assoc BoolCocycleModel
    (two_cocycle_simplex_unit 0) three_choice x y z).
Defined.
