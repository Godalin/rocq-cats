From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereFaceHomotopy
  Instance.Set.Simplicial.Homotopy.SphereCylinder
  Instance.Bool.CocycleSphereGroup
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Prism Faces and Independent Comparison Fillers

    The first prism tetrahedron has its endpoints in the low faces.
    Feed that actual tetrahedron into the new four-horn construction,
    then inspect every retained face and the converted homotopy. *)

(** * 实际棱柱面与独立比较填充

    第一块棱柱四面体的端点位于低索引面。将该实际四面体传入新四维 horn
    构造，再检查每个保留面及转换后的同伦。 *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

Definition label_sphere
  : TwoSphereS BoolCocycleModel (two_cocycle_simplex_unit 0)
  := cocycle_two_sphere_resp true.

(** Keep an actual relative cylinder, not a substituted degeneracy value. *)

(** 保留实际相对柱，不以退化值替代。 *)

Definition actual_cylinder
  : TwoSphereCylinderHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      label_sphere label_sphere
  := TwoSphereConstantCylinder BoolCocycleModel (two_cocycle_simplex_unit 0)
      label_sphere label_sphere (reflexivity label_sphere).

Definition first_prism
  : BoolCocycleModel 3
  := two_sphere_prism actual_cylinder fin_first.

(** In this constant-time cylinder the first prism is definitionally
    s₀ of its retained triangle. All four equations still use the ordinary
    simplicial identities, not equality between proof fields. *)

(** 此时间恒定柱的第一块棱柱定义为保留三角形的 s₀。四个方程仍使用通常单纯
    恒等式，不比较证明字段。 *)

Definition prism_low_homotopy
  : TwoSphereLowHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      label_sphere label_sphere.
Proof.
  exists first_prism. split; [| split; [| split]].
  - change (d[BoolCocycleModel; 2; fin_first]
      (s[BoolCocycleModel; 2; fin_first] label_sphere.1) ≈S label_sphere.1).
    exact (simplex_face_degeneracy_id (X := BoolCocycleModel)
      (fin_first : Ordinal 2) label_sphere.1).
  - change (d[BoolCocycleModel; 2; fin_first⁺]
      (s[BoolCocycleModel; 2; fin_first] label_sphere.1) ≈S label_sphere.1).
    exact (simplex_face_degeneracy_next (X := BoolCocycleModel)
      (fin_first : Ordinal 2) label_sphere.1).
  - exact (sphere_degenerate_first_high BoolCocycleModel
      (two_cocycle_simplex_unit 0) label_sphere fin_first).
  - exact (sphere_degenerate_first_high BoolCocycleModel
      (two_cocycle_simplex_unit 0) label_sphere fin_first⁺).
Defined.

Definition actual_horn
  := SphereLowHomotopyHornN BoolCocycleModel (two_cocycle_simplex_unit 0)
      prism_low_homotopy.

Definition actual_filler
  := horn_fill actual_horn.

Definition supplied_homotopy
  := SphereLowHomotopyOfFiller BoolCocycleModel (two_cocycle_simplex_unit 0)
      prism_low_homotopy actual_filler.1 actual_filler.2.

Definition chosen_homotopy
  := SphereLowHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      prism_low_homotopy.

Definition prism_class_step
  := two_sphere_low_homotopy_class BoolCocycleModel
      (two_cocycle_simplex_unit 0) prism_low_homotopy.

(** Reading all triangular faces checks their orientation and labels. *)

(** 读取全部三角形面，检查其定向与标签。 *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example prism_faces_compute
  : face_values first_prism = (true, true, false, false).
Proof. vm_compute. reflexivity. Defined.

Example comparison_faces_compute
  : (face_values (d[BoolCocycleModel; 3; fin_first] actual_filler.1),
     face_values (d[BoolCocycleModel; 3; fin_first⁺] actual_filler.1),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺] actual_filler.1),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺⁺] actual_filler.1),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺⁺⁺] actual_filler.1),
     face_values supplied_homotopy.1, face_values chosen_homotopy.1)
      = ((false, false, true, true), (false, false, true, true),
         (false, false, false, false), (true, true, false, false),
         (true, true, false, false), (false, false, true, true),
         (false, false, true, true)).
Proof. vm_compute. reflexivity. Defined.

(** ** Boolean-Valued Equality with Distinct Representatives

    These data ensure that conversion does not replace specified equality
    by native equality, identify boundary witnesses, or equate fillers. *)

(** ** 不同表示与布尔值相等

    这些数据确保转换不将指定相等替换为原生相等、不识别边界见证，也不等同填充。 *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation.
  split.
  - intros x. exact true.
  - intros x y E. exact E.
  - intros x y z E F. exact E.
Defined.

(** A constant simplicial object retains those representations in every degree. *)

(** 常值单纯对象在每一维保留这些表示。 *)

Definition WitnessX
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

(** Select one native Boolean in every requested horn, explicitly. *)

(** 显式为所请求 horn 选择一个原生布尔值。 *)

Program Definition WitnessHornFillers (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers WitnessX n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m z. exact true. Defined.

Fail Definition unchosen_comparison
  : HasHornFillers WitnessX 4 fin_first⁺
  := _.

Local Instance comparison_one
  : HasHornFillers WitnessX 4 fin_first⁺
  := WitnessHornFillers 4 fin_first⁺ false.

Fail Definition unchosen_three
  : HasHornFillers WitnessX 3 fin_first⁺⁺
  := _.

Fail Definition unchosen_full_Kan
  : HasKanFillers WitnessX
  := _.

Definition true_sphere
  : TwoSphereS WitnessX false
  := (true; λ i, false).

Definition false_sphere
  : TwoSphereS WitnessX false
  := (false; λ i, true).

Definition low_witness
  : TwoSphereLowHomotopy WitnessX false true_sphere false_sphere
  := (false; (true, (false, (true, false)))).

(** Supplied and selected fillers are deliberately different native values. *)

(** 给定与选定填充刻意具有不同原生值。 *)

Definition supplied_witness_filler
  := @horn_fill WitnessX 4 fin_first⁺
      (WitnessHornFillers 4 fin_first⁺ true)
      (SphereLowHomotopyHornN WitnessX false low_witness).

Definition converted_supplied
  := SphereLowHomotopyOfFiller WitnessX false low_witness
      supplied_witness_filler.1 supplied_witness_filler.2.

Definition converted_chosen
  := SphereLowHomotopy WitnessX false low_witness.

Example different_fillers_compute
  : (low_witness.1, supplied_witness_filler.1,
     converted_supplied.1, converted_chosen.1, true_sphere.1, false_sphere.1)
      = (false, true, true, false, true, false).
Proof. vm_compute. reflexivity. Defined.

(** The new class generator is actual conversion, not native reflexivity. *)

(** 新类生成元是实际转换，而非原生自反性。 *)

Definition different_representatives_class
  : (true_sphere : TwoSphereClassS WitnessX false) ≈S false_sphere
  := two_sphere_low_homotopy_class WitnessX false low_witness.

(** Endpoint Proper retains the exact original tetrahedron. *)

(** 端点 Proper 保留完全相同的原四面体。 *)

Definition replaced_witness
  := fst (TwoSphereLowHomotopy_proper WitnessX false
      true_sphere false_sphere (false : true_sphere ≈S false_sphere)
      false_sphere true_sphere (true : false_sphere ≈S true_sphere)) low_witness.

Example endpoint_replacement_computes
  : replaced_witness.1 = low_witness.1.
Proof. reflexivity. Defined.
