From Cats Require Import
  Instance.Set.Simplicial.Cocycle.SphereKanGroup
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.
Local Open Scope monoid_scope.

(** * The Same Boolean Model, Two Descriptions of Its Group

    Use actual Kan choices for the generic group and compare it with the
    coefficient-defined group. Reuse the original lifted setoid isomorphism
    and read both of its maps, rather than constructing another inverse. *)

(** * 同一布尔模型的两种群描述

    以实际 Kan 选择构造通用群，与系数定义群比较。复用原有提升广集同构并读取
    其两个映射，不重新构造逆。 *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolS_Group.
Local Existing Instance BoolS_IsCommutativeMonoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

Fail Definition unchosen_group
  : Group BoolCocycleSphereClassS
  := _.

(** Supply the three choices explicitly, retaining the actual model fillers. *)

(** 显式给出三个选择，保留实际模型填充。 *)

Definition three_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Definition left_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺⁺
  := _.

Definition right_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺
  := _.

Definition class_group
  : Group BoolCocycleSphereClassS
  := TwoSphereClassGroup BoolCocycleModel (two_cocycle_simplex_unit 0)
      three_choice left_choice right_choice.

Definition class_magma
  : Magma BoolCocycleSphereClassS
  := SemigroupM (MonoidSG (GroupM class_group)).

(** Even coefficient commutativity and full Kan do not enable the new
    class property globally. Its monoid parameter is the exact Group parent. *)

(** 即使系数交换且具备完整 Kan，也不会全局启用新类性质；幺半群参数为群的
    完全相同父结构。 *)

Fail Definition unchosen_commutativity
  : @IsCommutativeMonoid BoolCocycleSphereClassS (GroupM class_group)
  := _.

Definition class_commutativity
  : @IsCommutativeMonoid BoolCocycleSphereClassS (GroupM class_group)
  := cocycle_kan_IsCommutativeMonoid three_choice.

(** The general comparison consumes the exact generic group multiplication. *)

(** 一般比较消费通用群中完全相同的乘法。 *)

Example products_agree (x y : BoolCocycleSphereClassS)
  : @magma_mul _ class_magma x y ≈S cocycle_two_sphere_mul x y.
Proof. exact (cocycle_kan_mul_eq three_choice x y). Defined.

Example inverses_agree (x : BoolCocycleSphereClassS)
  : @group_inv _ class_group x ≈S cocycle_two_sphere_inv x.
Proof. exact (cocycle_kan_left_inverse_eq left_choice x). Defined.

(** The existing classification maps now preserve the generic product. *)

(** 既有分类映射现在保持通用乘积。 *)

Example decoding_preserves_product (x y : BoolCocycleSphereClassS)
  : cocycle_two_sphere_class_value_resp (@magma_mul _ class_magma x y) ≈S
      cocycle_two_sphere_class_value_resp x ⋅
        cocycle_two_sphere_class_value_resp y.
Proof. exact (cocycle_kan_mul_value three_choice x y). Defined.

Example encoding_preserves_product (a b : bool)
  : cocycle_two_sphere_class_resp (a ⋅ b) ≈S
      @magma_mul _ class_magma
        (cocycle_two_sphere_class_resp a) (cocycle_two_sphere_class_resp b).
Proof. exact (cocycle_kan_class_mul three_choice a b). Defined.

(** The new property proves the model law on that same inherited magma. *)

(** 新性质在同一个继承原群上证明模型定律。 *)

Example model_multiplication_commutes (x y : BoolCocycleSphereClassS)
  : @magma_mul _ class_magma x y ≈S @magma_mul _ class_magma y x.
Proof.
  exact (@monoid_mul_comm _ (GroupM class_group) class_commutativity x y).
Defined.

(** Preserve actual Kan computations while reading their coefficients. *)

(** 读取系数时保留实际 Kan 计算。 *)

Definition product_values (a b : bool)
  : bool * bool
  := (cocycle_two_sphere_class_value_resp
        (@magma_mul _ class_magma
          (cocycle_two_sphere_resp a) (cocycle_two_sphere_resp b)),
      cocycle_two_sphere_class_value_resp
        (cocycle_two_sphere_mul
          (cocycle_two_sphere_resp a) (cocycle_two_sphere_resp b))).

Definition inverse_values (a : bool)
  : bool * bool
  := (cocycle_two_sphere_class_value_resp
        (@group_inv _ class_group (cocycle_two_sphere_resp a)),
      cocycle_two_sphere_class_value_resp
        (cocycle_two_sphere_inv (cocycle_two_sphere_resp a))).

Example operations_compute
  : (product_values false false, product_values false true,
     product_values true false, product_values true true,
     inverse_values false, inverse_values true)
      = ((false, false), (true, true), (true, true), (false, false),
         (false, false), (true, true)).
Proof. vm_compute. reflexivity. Defined.

(** This is the original classification isomorphism at common upward bounds. *)

(** 这是在共同向上界处的原有分类同构。 *)

Definition underlying_iso
  : ↑S BoolCocycleSphereClassS ≅[SetCat] ↑S BoolS
  := cocycle_two_sphere_class_iso.

Definition iso_decode (a : bool)
  : bool
  := lower (underlying_iso.1 {|lower := cocycle_two_sphere_resp a|}).

Definition iso_encode_value (a : bool)
  : bool
  := cocycle_two_sphere_class_value_resp
      (lower (underlying_iso.2.1 {|lower := a|})).

Example original_iso_computes
  : (iso_decode false, iso_decode true, iso_encode_value false,
     iso_encode_value true) = (false, true, false, true).
Proof. vm_compute. reflexivity. Defined.
