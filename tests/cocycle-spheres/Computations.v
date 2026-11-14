From Cats Require Import
  Algebra.Group.Cocycle
  Instance.Bool.CocycleSphere.

Local Open Scope ordinal_scope.

(** * Retained Representatives and Tetrahedron Computation

    Importing the comparison does not select a Boolean coefficient group
    or Kan structure. The selected sphere representatives and actual
    elementary homotopy tetrahedron nevertheless remain transparent. *)

(** * 保留代表与四面体计算

    导入比较不会选定布尔系数群或 Kan 结构；选定球面代表及实际初等同伦
    四面体仍保持透明。 *)

Fail Definition unchosen_boolean_group
  : Group BoolS
  := _.

Fail Definition unchosen_boolean_Kan
  : HasKanFillers BoolCocycleModel
  := _.

(** Constructing and then decoding a class computes its original label. *)

(** 先构造类再读取，计算出原标签。 *)

Example class_label_computes (a : bool)
  : cocycle_two_sphere_class_value_resp
      (@cocycle_two_sphere_class_resp BoolS BoolS_Monoid a
        : BoolCocycleSphereClassS) = a.
Proof. reflexivity. Defined.

(** Decoding the distinguished sphere computes the Boolean unit. *)

(** 读取指定球面，计算出布尔单位。 *)

Example base_label_computes
  : cocycle_two_sphere_class_value_resp
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)) = false.
Proof. reflexivity. Defined.

(** Retain an actual homotopy between two copies of the true sphere. *)

(** 保留真球面两个副本之间的实际同伦。 *)

Definition true_sphere_homotopy
  : TwoSphereHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      bool_cocycle_sphere bool_cocycle_sphere
  := CocycleTwoSphereHomotopy
      bool_cocycle_sphere bool_cocycle_sphere eq_refl.

(** Both constant faces and both nonconstant endpoint faces compute from
    the retained tetrahedron, rather than just from its law witnesses. *)

(** 两个常值面与两个非常值端点面均由保留四面体计算，而非仅由定律见证得出。 *)

Example homotopy_faces_compute
  : (two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first] true_sphere_homotopy.1),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺] true_sphere_homotopy.1),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺] true_sphere_homotopy.1),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] true_sphere_homotopy.1)) =
      (false, false, true, true).
Proof. reflexivity. Defined.
