From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereSecondTransport
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Transport and a Generated Chain

    Build the input homotopy using the already proved four-horn comparison
    between a generic selected product and a coefficient-built product.
    Both new transports consume the actual Boolean Kan fillers. The finite
    generated chain contains equality, homotopy, symmetry and transitivity;
    computing its returned tetrahedron exercises the existing closure fold. *)

(** * 实际运输与一条生成链

    用已证明的四维 horn 比较，得到通用选定乘积与系数直接乘积之间的输入同伦。
    两个新运输均消费实际布尔 Kan 填充。有限生成链包含相等、同伦、对称与传递，
    计算其返回四面体实际消费既有闭包折叠。 *)

Fail Definition unchosen_group
  : Group BoolS
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Fail Definition unchosen_forward_horn
  : HasHornFillers BoolCocycleModel 4 fin_first⁺⁺⁺⁺
  := _.

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

(** The two input representatives have coefficient true, but come from
    different constructions. Their boundary witnesses are retained. *)

(** 两个输入代表的系数为 true，但来自不同构造；保留其边界见证。 *)

Definition selected_input
  := SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
      (cocycle_two_sphere_resp false) (cocycle_two_sphere_resp true).

Definition direct_input
  := cocycle_two_sphere_mul
      (cocycle_two_sphere_resp false) (cocycle_two_sphere_resp true).

(** The input homotopy is an actual tetrahedron from the earlier comparison. *)

(** 输入同伦是先前比较给出的实际四面体。 *)

Definition input_homotopy
  : TwoSphereHomotopy BoolCocycleModel (two_cocycle_simplex_unit 0)
      selected_input.1 direct_input
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit 0) selected_input.2
      (CocycleTwoSphereMul (cocycle_two_sphere_resp false)
        (cocycle_two_sphere_resp true)).

(** Fix the true-labelled first input and vary the second representative. *)

(** 固定 true 标签的第一输入，改变第二输入代表。 *)

Definition initial_composite
  := CocycleTwoSphereMul (cocycle_two_sphere_resp true) selected_input.1.

(** Transport forward, then back, retaining the same output representative. *)

(** 正向运输再反向返回，保留相同输出代表。 *)

Definition forward_composite
  := SphereCompositeSecondHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit 0) input_homotopy initial_composite.

Definition backward_composite
  := SphereCompositeSecondHomotopyBack BoolCocycleModel
      (two_cocycle_simplex_unit 0) input_homotopy forward_composite.

(** Keep an explicit generated derivation; it is not replaced by reflexivity. *)

(** 保留显式生成推导，不用自反性替换该推导。 *)

Definition input_chain
  : (selected_input.1 : BoolCocycleSphereClassS) ≈S direct_input
  := closure_trans (closure_refl selected_input.1)
      (closure_trans (two_sphere_class_eq BoolCocycleModel
        (two_cocycle_simplex_unit 0) (reflexivity selected_input.1))
        (closure_trans (two_sphere_class_step BoolCocycleModel
          (two_cocycle_simplex_unit 0) input_homotopy)
          (closure_trans (closure_sym (two_sphere_class_step BoolCocycleModel
            (two_cocycle_simplex_unit 0) input_homotopy))
            (two_sphere_class_step BoolCocycleModel
              (two_cocycle_simplex_unit 0) input_homotopy)))).

(** Fold the whole chain into a new actual composite tetrahedron. *)

(** 把整条链折叠为新的实际合成四面体。 *)

Definition chain_composite
  := fst (two_sphere_composite_second_class BoolCocycleModel
      (two_cocycle_simplex_unit 0) input_chain
      (cocycle_two_sphere_resp true)
      (cocycle_two_sphere_mul (cocycle_two_sphere_resp true) selected_input.1))
      initial_composite.

(** Read all triangle faces, including nonconstant input and context faces. *)

(** 读取全部三角形面，包括非常值的输入及上下文面。 *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example transports_compute
  : (face_values input_homotopy.1, face_values forward_composite.1,
     face_values backward_composite.1, face_values chain_composite.1)
      = ((false, false, true, true), (false, true, false, true),
         (false, true, false, true), (false, true, false, true)).
Proof. vm_compute. reflexivity. Defined.

(** A three-horn choice is explicit data, not a new registered instance. *)

(** 三维 horn 选择为显式数据，不注册新实例。 *)

Definition three_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

(** The partial class operation retains the selected product computation. *)

(** 类上偏运算保留选定乘积的计算。 *)

Definition partial_value (a b : bool)
  : bool
  := cocycle_two_sphere_class_value_resp
      (two_sphere_kan_composite_second_resp BoolCocycleModel
        (two_cocycle_simplex_unit 0) three_choice
        (cocycle_two_sphere_resp a) (cocycle_two_sphere_resp b)).

Example partial_operation_computes
  : (partial_value false false, partial_value false true,
     partial_value true false, partial_value true true)
      = (false, true, true, false).
Proof. vm_compute. reflexivity. Defined.

(** Consume the actual class-map Proper field on the full generated chain. *)

(** 用实际类映射的 Proper 字段消费完整生成链。 *)

Example partial_preserves_chain
  : two_sphere_kan_composite_second_resp BoolCocycleModel
      (two_cocycle_simplex_unit 0) three_choice (cocycle_two_sphere_resp true)
      selected_input.1 ≈S
      two_sphere_kan_composite_second_resp BoolCocycleModel
        (two_cocycle_simplex_unit 0) three_choice (cocycle_two_sphere_resp true)
        direct_input.
Proof. apply func_proper. exact input_chain. Defined.
