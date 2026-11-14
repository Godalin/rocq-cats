From Cats Require Import
  Cat.Core
  Instance.Bool.CocycleSphereCylinder.

Import Cats.Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Cylinder Constructed from a Tetrahedron Generator

    The class equality below is a retained tetrahedron step, not native
    reflexivity. The resulting cylinder must still compute without
    normalizing equality witnesses or losing its spatial/time coordinates. *)

(** * 从四面体生成元构造的柱

    下方类相等是保留四面体的一步，而非原生自反性。所得柱仍须可计算，无须
    归一化相等见证，也不丢失空间／时间坐标。 *)

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

(** Freely label a retained representative at the model's native sizes. *)

(** 在模型原生大小中为保留代表自由标记。 *)

Definition label_sphere (a : bool)
  : BoolCocycleSphereClassS
  := cocycle_two_sphere_class_resp a.

(** An actual elementary tetrahedron gives the class witness supplied to
    the reverse cylinder comparison. *)

(** 实际初等四面体给出传入反向柱比较的类见证。 *)

Definition label_cylinder (a : bool)
  : TwoSphereCylinderHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      (label_sphere a) (label_sphere a)
  := CocycleTwoSphereCylinder (label_sphere a) (label_sphere a)
      (two_sphere_class_step BoolCocycleModel (two_cocycle_simplex_unit 0)
        (CocycleTwoSphereHomotopy (label_sphere a) (label_sphere a) eq_refl)).

(** Every time operator computes the same triangle coefficient. *)

(** 每个时间算子都计算出同一个三角形系数。 *)

Example cylinder_value_computes (a : bool) (t : (@Hom Δ) 2 1%nat)
  : two_cocycle_triangle_value_resp
      (two_sphere_cylinder_eval BoolCocycleModel (two_cocycle_simplex_unit 0)
        (label_cylinder a) id t) = a.
Proof. reflexivity. Defined.

(** Read a face of one of the three actual prism tetrahedra. *)

(** 读取三个实际棱柱四面体之一的一个面。 *)

Definition prism_face_value (a : bool) (i : Ordinal 2) (j : Ordinal 3)
  : bool
  := two_cocycle_triangle_value_resp
      (d[BoolCocycleModel; 2; j] (two_sphere_prism (label_cylinder a) i)).

(** All twelve coefficients compute with the expected staircase orientation.
    This checks the actual maps, not only the proved face equations. *)

(** 全部十二个系数按预期阶梯定向计算。这检查实际映射，而非仅检查已证明的
    面方程。 *)

Example prism_faces_compute (a : bool)
  : ((prism_face_value a fin_first fin_first,
      prism_face_value a fin_first fin_first⁺,
      prism_face_value a fin_first fin_first⁺⁺,
      prism_face_value a fin_first fin_first⁺⁺⁺),
     (prism_face_value a fin_first⁺ fin_first,
      prism_face_value a fin_first⁺ fin_first⁺,
      prism_face_value a fin_first⁺ fin_first⁺⁺,
      prism_face_value a fin_first⁺ fin_first⁺⁺⁺),
     (prism_face_value a fin_first⁺⁺ fin_first,
      prism_face_value a fin_first⁺⁺ fin_first⁺,
      prism_face_value a fin_first⁺⁺ fin_first⁺⁺,
      prism_face_value a fin_first⁺⁺ fin_first⁺⁺⁺)) =
      ((a, a, false, false), (false, a, a, false), (false, false, a, a)).
Proof. reflexivity. Defined.
