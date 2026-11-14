From Cats Require Import
  Algebra.Group.Cocycle
  Instance.Bool.Commutative.

Local Open Scope monoid_scope.

(** * Actual Boolean Completion Labels

    Importing the theory does not choose a coefficient structure. The
    concrete checks below then enable the existing Boolean group locally
    and inspect the selected labels, rather than their proof fields. *)

(** * 实际布尔补全标签

    导入理论不会选定系数结构。随后具体检查局部启用已有布尔群，读取选定
    标签，而不比较证明字段。 *)

Fail Definition unchosen_boolean_group
  : Group BoolS
  := _.

Fail Definition unchosen_boolean_commutativity
  : @IsCommutativeMonoid BoolS BoolS_Monoid
  := _.

Local Existing Instance BoolS_Group.

(** The first projection computes without unfolding an opaque theorem. *)

(** 第一投影不需要展开不透明定理即可计算。 *)

Example first_label_computes
  : (Cocycle012Solution true true false).1 = false.
Proof. reflexivity. Defined.

(** Solving for the second label retains a nonunit answer. *)

(** 第二个标签的求解保留非单位答案。 *)

Example second_label_computes
  : (Cocycle023Solution true false false).1 = true.
Proof. reflexivity. Defined.

(** Reorienting the equation does not obscure the third computation. *)

(** 方程换向不遮蔽第三个计算。 *)

Example third_label_computes
  : (Cocycle123Solution true true false).1 = false.
Proof. reflexivity. Defined.

(** The fourth completion also remains transparent. *)

(** 第四个补全也保持透明。 *)

Example last_label_computes
  : (Cocycle013Solution false true false).1 = true.
Proof. reflexivity. Defined.
