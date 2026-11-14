From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereKan
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Consuming the Existing Full Boolean Kan Selection

    The generic constructions must use the actual supplied Kan fillers.
    Their Boolean coefficients compute xor and inverse; the full witnessing
    tetrahedra must compute the four faces with the declared orientation.
    These concrete checks do not prove choice independence for arbitrary
    Kan objects. *)

(** * 消费既有完整布尔 Kan 选择

    通用构造必须使用实际给定的 Kan 填充。其布尔系数计算为异或及逆，完整
    见证四面体的四个面也必须按声明定向计算。这些具体检查不证明任意 Kan
    对象的选择独立性。 *)

Fail Definition unchosen_group
  : Group BoolS
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Fail Definition unchosen_three_horn
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Read the coefficient from the generic selected composite sphere. *)

(** 从通用选定合成球面读取系数。 *)

Definition selected_product_value (a b : bool)
  : bool
  := cocycle_two_sphere_value_resp
      (SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
        (cocycle_two_sphere_resp a) (cocycle_two_sphere_resp b)).1.

(** All four products compute using the actual full Kan selection. *)

(** 全部四个乘积使用实际完整 Kan 选择计算。 *)

Example products_compute
  : (selected_product_value false false, selected_product_value false true,
     selected_product_value true false, selected_product_value true true)
      = (false, true, true, false).
Proof. vm_compute. reflexivity. Defined.

(** Read both independent inverse candidates. *)

(** 读取两个独立逆候选。 *)

Definition selected_inverse_values (a : bool)
  : bool * bool
  := (cocycle_two_sphere_value_resp
        (SphereKanRightInverse BoolCocycleModel (two_cocycle_simplex_unit 0)
          (cocycle_two_sphere_resp a)).1,
      cocycle_two_sphere_value_resp
        (SphereKanLeftInverse BoolCocycleModel (two_cocycle_simplex_unit 0)
          (cocycle_two_sphere_resp a)).1).

(** Both candidates compute the expected Boolean inverse. *)

(** 两个候选均计算出预期布尔逆。 *)

Example inverses_compute
  : (selected_inverse_values false, selected_inverse_values true)
      = ((false, false), (true, true)).
Proof. vm_compute. reflexivity. Defined.

(** Read all four actual faces, rather than only their stored equations. *)

(** 读取全部四个实际面，而非仅检查其保存方程。 *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

(** Product and both inverse witnesses have the declared face roles. *)

(** 乘积与两个逆见证均具有声明的面角色。 *)

Example retained_tetrahedra_compute
  : (face_values
        (SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
          bool_cocycle_sphere bool_cocycle_sphere).2.1,
     face_values
        (SphereKanRightInverse BoolCocycleModel (two_cocycle_simplex_unit 0)
          bool_cocycle_sphere).2.1,
     face_values
        (SphereKanLeftInverse BoolCocycleModel (two_cocycle_simplex_unit 0)
          bool_cocycle_sphere).2.1)
      = ((false, true, false, true),
         (false, true, false, true), (false, true, false, true)).
Proof. vm_compute. reflexivity. Defined.
