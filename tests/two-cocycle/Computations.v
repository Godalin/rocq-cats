From Cats Require Import
  Instance.Bool.Cocycle
  Cat.Shape.Ordinal.

(** * A Nonzero Triangle Label

    In the ordered triangle [Ord 2], mark only the long edge 0 to 2.
    Its coboundary labels the triangle by [true]. Triangles with identity
    short edges still have label [false]. These tests inspect computations,
    rather than proving general equations already in the theory modules. *)

(** * 一个非零三角形标签

    在有序三角形 [Ord 2] 中只标记从零到二的长边，余边界便将三角形标为
    [true]，含恒等短边的三角形仍标为 [false]。这些测试检查计算见证，不重复
    理论模块已有的一般方程。 *)

(** Importing the example must not implicitly select its coefficient monoid. *)

(** 导入例子不得隐式选定系数幺半群。 *)

Fail Definition unchosen_boolean_monoid
  : Monoid BoolS
  := ltac:(typeclasses eauto).

Example triangle_label_computes
  : BoolTriangleCocycle⟦ordinal_step (@fin_first 1),
      ordinal_step (fin_next (@fin_first 0))⟧₂ = true.
Proof. reflexivity. Qed.

Example identity_triangle_computes
  : BoolTriangleCocycle⟦@Cat.Core.id [Ord 2] fin_first,
      ordinal_step (@fin_first 1)⟧₂ = false.
Proof. reflexivity. Qed.

Example pulled_back_label_computes
  : (TwoCocyclePullback IdF BoolTriangleCocycle)⟦
      ordinal_step (@fin_first 1),
      ordinal_step (fin_next (@fin_first 0))⟧₂ = true.
Proof. reflexivity. Qed.

Example constant_label_computes
  : (@UnitTwoCocycle [Ord 2] BoolS BoolS_Monoid)⟦
      ordinal_step (@fin_first 1),
      ordinal_step (fin_next (@fin_first 0))⟧₂ = false.
Proof. reflexivity. Qed.
