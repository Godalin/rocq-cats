From Cats Require Import
  Algebra.Group.Equation
  Instance.Bool.Commutative.

Local Open Scope monoid_scope.

(** * Explicitly Selected Boolean Coefficients

    Importing coefficients must not make their chosen structures automatic.
    After local enabling, solution projections should compute actual bits. *)

(** * 显式选定的布尔系数

    导入系数不得自动选取其结构。局部启用后，解的投影应计算出实际布尔位。 *)

Fail Definition unchosen_boolean_group
  : Group BoolS
  := ltac:(typeclasses eauto).

Fail Definition unchosen_boolean_commutativity
  : @IsCommutativeMonoid BoolS BoolS_Monoid
  := ltac:(typeclasses eauto).

(** ** Computing the Selected Solutions

    Enable the existing xor group and its commutativity witness locally,
    checking that both refer to the same underlying multiplication. *)

(** ** 计算选定解

    局部启用已有异或群及其交换性见证，检查两者使用同一底层乘法。 *)

Section BooleanComputations.
Local Existing Instance BoolS_Group.
Local Existing Instance BoolS_IsCommutativeMonoid.

Example left_solution_computes
  : (GroupMulLSolution (G := BoolS) true false).1 = true.
Proof. reflexivity. Qed.

Example right_solution_computes
  : (GroupMulRSolution (G := BoolS) true false).1 = true.
Proof. reflexivity. Qed.

Example left_solution_map_computes
  : group_mul_l_solve_resp (G := BoolS) true true = false.
Proof. reflexivity. Qed.

Example right_solution_map_computes
  : group_mul_r_solve_resp (G := BoolS) false true = true.
Proof. reflexivity. Qed.

(** The group and commutativity witnesses infer coherently without a second
    explicitly enabled monoid instance. *)

(** 群和交换性见证能够相干推断，无须再显式启用第二个幺半群实例。 *)

Definition boolean_interchange (a b c d : BoolS)
  : (a ⋅ b) ⋅ (c ⋅ d) ≈S (a ⋅ c) ⋅ (b ⋅ d)
  := monoid_mul_interchange a b c d.

End BooleanComputations.
