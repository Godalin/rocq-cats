From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereKanComparison
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Comparing Generic and Coefficient-Built Tetrahedra

    One composite is selected by the actual Boolean Kan filler; the other
    is built directly by the existing cocycle product construction. Their
    comparison uses the generic four-horn filler, not coefficient equality
    as a replacement for a homotopy. *)

(** * 比较通用与系数构造的四面体

    一份合成由实际布尔 Kan 填充选择，另一份由既有 cocycle 乘积直接构造。
    比较使用通用四维 horn 填充，不以系数相等代替同伦。 *)

Fail Definition unchosen_group
  : Group BoolS
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Fail Definition unchosen_four_horn
  : HasHornFillers BoolCocycleModel 4 fin_first⁺⁺
  := _.

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

(** The generic selected composite, retaining its tetrahedron. *)

(** 保留四面体的通用选定合成。 *)

Definition selected (a b : bool)
  : ∃ z : TwoSphereS BoolCocycleModel (two_cocycle_simplex_unit 0),
      TwoSphereComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
        (cocycle_two_sphere_resp a) (cocycle_two_sphere_resp b) z
  := SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
      (cocycle_two_sphere_resp a) (cocycle_two_sphere_resp b).

(** The direct product composite uses the existing coefficient construction. *)

(** 直接乘积合成使用既有系数构造。 *)

Definition direct (a b : bool)
  : TwoSphereComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
      (cocycle_two_sphere_resp a) (cocycle_two_sphere_resp b)
      (cocycle_two_sphere_mul (cocycle_two_sphere_resp a)
        (cocycle_two_sphere_resp b))
  := CocycleTwoSphereMul (cocycle_two_sphere_resp a)
      (cocycle_two_sphere_resp b).

(** Retain the elementary comparison homotopy itself. *)

(** 保留初等比较同伦本身。 *)

Definition comparison (a b : bool)
  : TwoSphereHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      (selected a b).1
      (cocycle_two_sphere_mul (cocycle_two_sphere_resp a)
        (cocycle_two_sphere_resp b))
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit 0) (selected a b).2 (direct a b).

(** Read the four actual triangle faces of a tetrahedron. *)

(** 读取四面体的四个实际三角形面。 *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

(** All four products give homotopies with two constant faces and the two
    output triangles, in the asserted orientation. *)

(** 四个乘积都得到定向正确的同伦：两个常值面及两个输出三角形。 *)

Example comparison_faces_compute
  : (face_values (comparison false false).1,
     face_values (comparison false true).1,
     face_values (comparison true false).1,
     face_values (comparison true true).1)
      = ((false, false, false, false), (false, false, true, true),
         (false, false, true, true), (false, false, false, false)).
Proof. vm_compute. reflexivity. Defined.

(** Read the actual selected four-simplex before taking its omitted face. *)

(** 在提取缺失面之前读取实际选定四维单形。 *)

Definition comparison_volume (a b : bool)
  : BoolCocycleModel 4
  := (horn_fill (SphereCompositeComparisonHornN BoolCocycleModel
      (two_cocycle_simplex_unit 0) (selected a b).2 (direct a b))).1.

(** All five tetrahedra compute, including the formerly omitted homotopy. *)

(** 五个四面体均可计算，包括原先缺失的同伦面。 *)

Example volume_faces_compute
  : (face_values (d[BoolCocycleModel; 3; fin_first]
        (comparison_volume true true)),
     face_values (d[BoolCocycleModel; 3; fin_first⁺]
        (comparison_volume true true)),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺]
        (comparison_volume true true)),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺⁺]
        (comparison_volume true true)),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺⁺⁺]
        (comparison_volume true true)))
      = ((false, false, false, false), (false, false, true, true),
         (false, false, false, false), (false, true, false, true),
         (false, true, false, true)).
Proof. vm_compute. reflexivity. Defined.

(** The new generated class equation is consumed by the existing coefficient
    evaluator; no axiom about the two filler records is available. *)

(** 既有系数求值消费新的生成类方程；没有等同两个填充记录的公理。 *)

Example comparison_class_evaluates (a b : bool)
  : cocycle_two_sphere_class_value_resp (selected a b).1 ≈S
      cocycle_two_sphere_class_value_resp
        (cocycle_two_sphere_mul (cocycle_two_sphere_resp a)
          (cocycle_two_sphere_resp b)).
Proof.
  apply func_proper. exact (two_sphere_composite_output_eq BoolCocycleModel
    (two_cocycle_simplex_unit 0) (selected a b).2 (direct a b)).
Defined.
