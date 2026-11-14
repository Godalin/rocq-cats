From Cats Require Import
  Instance.Bool.CocycleSphereGroup.

Local Open Scope ordinal_scope.
Local Open Scope monoid_scope.

(** * Explicit Selection and Geometric Computation

    Importing the new group construction must not enable either the
    coefficient group, the class monoid/group, or the Kan structure.
    Once enabled locally, multiplication must compute xor and an actual
    retained composition tetrahedron must compute all four face labels. *)

(** * 显式选择与几何计算

    导入新群构造不得启用系数群、类幺半群／群或 Kan 结构。局部启用后，
    乘法须计算异或，实际保留合成四面体须计算全部四个面标签。 *)

Fail Definition unchosen_coefficient_group
  : Group BoolS
  := _.

Fail Definition unchosen_class_monoid
  : Monoid BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_class_group
  : Group BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolS_Group.
Local Existing Instance BoolCocycleSphereClassS_Group.
Local Existing Instance BoolCocycleModel_HasKanFillers.

(** The bundled multiplication computes xor on any two Boolean labels. *)

(** 打包乘法在任意两个布尔标签上计算异或。 *)

Example class_product_computes (a b : bool)
  : cocycle_two_sphere_class_value_resp
      ((@cocycle_two_sphere_class_resp BoolS BoolS_Monoid a : BoolCocycleSphereClassS) ⋅
        @cocycle_two_sphere_class_resp BoolS BoolS_Monoid b) = xorb a b.
Proof. reflexivity. Defined.

(** The bundled inverse is computational, with no opaque inverse choice. *)

(** 打包逆可计算，不带不透明的逆选择。 *)

Example class_inverse_computes (a : bool)
  : cocycle_two_sphere_class_value_resp
      ((@cocycle_two_sphere_class_resp BoolS BoolS_Monoid a : BoolCocycleSphereClassS)⁻¹) = a.
Proof. reflexivity. Defined.

(** The actual constant sphere is the bundled unit. *)

(** 实际常值球面就是打包单位。 *)

Example class_unit_computes
  : cocycle_two_sphere_class_value_resp (1 : BoolCocycleSphereClassS) = false.
Proof. reflexivity. Defined.

(** The square tetrahedron retains one constant face, the product face,
    and both nonzero input faces in the expected orientation. *)

(** 平方四面体按预期定向保留一个常值面、乘积面及两个非零输入面。 *)

Example square_faces_compute
  : (two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first] BoolCocycleSphereSquare.1),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺] BoolCocycleSphereSquare.1),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺] BoolCocycleSphereSquare.1),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] BoolCocycleSphereSquare.1)) =
      (false, true, false, true).
Proof. reflexivity. Defined.

(** Apply the general independence theorem to the previously constructed
    full Kan choice, not just to our explicit tetrahedron. *)

(** 将一般选择无关定理用于先前构造的完整 Kan 选择，而非仅用于显式四面体。 *)

Example chosen_Kan_product_class
  : (cocycle_two_sphere_face
      (horn_fill (cocycle_two_sphere_horn
        bool_cocycle_sphere bool_cocycle_sphere)).1
      : BoolCocycleSphereClassS) ≈S 1.
Proof.
  transitivity (cocycle_two_sphere_mul bool_cocycle_sphere bool_cocycle_sphere).
  - apply cocycle_two_sphere_horn_unique. apply (horn_fill _).2.
  - exact bool_cocycle_sphere_square.
Defined.
