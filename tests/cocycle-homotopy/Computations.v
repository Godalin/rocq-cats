From Cats Require Import
  Instance.Bool.CocycleHomotopy
  Cat.Core.

Import Cats.Cat.Core.

Local Open Scope nat_scope.

(** * Actual Map Data Survive the Homotopy Invariant

    Importing the obstruction must not enable chosen structures. The
    computations below inspect an actual precomposed homotopy at arbitrary
    time and evaluate a map while retaining a nontrivial chain witness. *)

(** * 同伦不变量保留实际映射数据

    导入障碍不得启用选定结构。以下计算在任意时间检查实际预复合同伦，并在
    保留非平凡链见证时对映射求值。 *)

Fail Definition unchosen_coefficient_group
  : Group BoolS
  := _.

Fail Definition unchosen_class_group
  : Group BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolS_Monoid.

(** Evaluate the original constant homotopy restricted to a free sphere. *)

(** 对限制到自由球面的原常值同伦求值。 *)

Example restricted_homotopy_computes (a : bool)
    (t : (@Hom Δ) 2 1%nat)
  : two_cocycle_triangle_value_resp
      (two_sphere_cylinder_eval BoolCocycleModel (two_cocycle_simplex_unit 0)
        (CocycleHomotopySphereCylinder
          (SimplicialConstantHomotopy (idN : BoolCocycleModel ⇒ BoolCocycleModel))
          (two_cocycle_simplex_unit 0) (cocycle_two_sphere_resp a)) id t) = a.
Proof. reflexivity. Defined.

(** A finite chain retains both a whole homotopy and natural equality,
    including a reversed step. This does not reverse the simplicial interval. *)

(** 有限链保留整份同伦与自然相等，还包含反向步；不反转单纯区间。 *)

Definition identity_chain
  : (idN : @CocycleHomotopyMapS BoolS BoolS_Monoid BoolCocycleModel) ≈S idN.
Proof.
  transitivity (idN : BoolCocycleModel ⇒ BoolCocycleModel).
  - exact (cocycle_homotopy_map_step (SimplicialConstantHomotopy idN)).
  - symmetry. apply cocycle_homotopy_map_eq. reflexivity.
Defined.

(** Evaluation still computes on either representative of that chain. *)

(** 求值在该链的任一代表上仍可计算。 *)

Example chain_evaluation_computes (a : bool)
  : @cocycle_homotopy_evaluation_resp BoolS BoolS_Monoid BoolCocycleModel
      (two_cocycle_simplex_unit 0) (cocycle_two_sphere_resp a) idN = a.
Proof. reflexivity. Defined.

(** Consume the chain through respectfulness, without discarding it or
    selecting any Kan filler. *)

(** 经保相等性消费该链，不丢弃它，也不选择 Kan 填充。 *)

Definition chain_evaluation_equality (a : bool)
  : a = a
  := @func_proper _ _
      (@cocycle_homotopy_evaluation_resp BoolS BoolS_Monoid BoolCocycleModel
        (two_cocycle_simplex_unit 0) (cocycle_two_sphere_resp a))
      _ _ identity_chain.
