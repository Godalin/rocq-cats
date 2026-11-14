From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereMagma
  Instance.Set.Magma
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Two Actual Input Chains and the Packaged Multiplication

    Both input equalities retain explicit generated derivations from
    actual four-horn comparisons. Transport them together, inspect the
    resulting tetrahedron, and consume the packaged product map's Proper
    field on that pair. Raw operations remain selected Kan computations. *)

(** * 两条实际输入链与打包后的乘法

    两个输入相等均保留来自实际四维 horn 比较的显式生成推导。将它们一起运输，
    检查返回四面体，再在这对输入链上消费打包积映射的 Proper 字段。原始运算
    始终保留选定 Kan 计算。 *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Fail Definition unchosen_outer_horn
  : HasHornFillers BoolCocycleModel 4 fin_first⁺⁺⁺⁺
  := _.

Local Existing Instance BoolS_Monoid.
Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Even after enabling all Kan choices, class magma selection stays
    explicit rather than becoming a model instance. *)

(** 即使启用全部 Kan 选择，类原群仍须显式选择，不成为模型实例。 *)

Fail Definition unchosen_class_magma
  : Magma BoolCocycleSphereClassS
  := _.

(** Two selected composites with swapped inputs yield true-labelled
    representatives, independently compared to their direct products. *)

(** 两份交换输入后的选定合成给出 true 标签代表，分别与其直接乘积比较。 *)

Definition first_input
  := SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
      (cocycle_two_sphere_resp false) (cocycle_two_sphere_resp true).

Definition second_input
  := SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
      (cocycle_two_sphere_resp true) (cocycle_two_sphere_resp false).

Definition first_direct
  := cocycle_two_sphere_mul
      (cocycle_two_sphere_resp false) (cocycle_two_sphere_resp true).

Definition second_direct
  := cocycle_two_sphere_mul
      (cocycle_two_sphere_resp true) (cocycle_two_sphere_resp false).

(** These homotopies are the actual output comparison tetrahedra. *)

(** 这些同伦就是实际输出比较四面体。 *)

Definition first_homotopy
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit 0) first_input.2
      (CocycleTwoSphereMul (cocycle_two_sphere_resp false)
        (cocycle_two_sphere_resp true)).

Definition second_homotopy
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit 0) second_input.2
      (CocycleTwoSphereMul (cocycle_two_sphere_resp true)
        (cocycle_two_sphere_resp false)).

(** The first derivation explicitly retains equality, symmetry and
    transitivity in addition to its elementary homotopy. *)

(** 第一推导在初等同伦之外显式保留相等、对称和传递。 *)

Definition first_chain
  : (first_input.1 : BoolCocycleSphereClassS) ≈S first_direct
  := closure_trans (closure_refl first_input.1)
      (closure_trans (two_sphere_class_eq BoolCocycleModel
        (two_cocycle_simplex_unit 0) (reflexivity first_input.1))
        (closure_trans (two_sphere_class_step BoolCocycleModel
          (two_cocycle_simplex_unit 0) first_homotopy)
          (closure_trans (closure_sym (two_sphere_class_step BoolCocycleModel
            (two_cocycle_simplex_unit 0) first_homotopy))
            (two_sphere_class_step BoolCocycleModel
              (two_cocycle_simplex_unit 0) first_homotopy)))).

(** The second argument also changes along a retained actual derivation. *)

(** 第二参数也沿保留的实际推导改变。 *)

Definition second_chain
  : (second_input.1 : BoolCocycleSphereClassS) ≈S second_direct
  := closure_trans (closure_refl second_input.1)
      (closure_trans (two_sphere_class_step BoolCocycleModel
        (two_cocycle_simplex_unit 0) second_homotopy)
        (closure_trans (closure_sym (two_sphere_class_step BoolCocycleModel
          (two_cocycle_simplex_unit 0) second_homotopy))
          (two_sphere_class_step BoolCocycleModel
            (two_cocycle_simplex_unit 0) second_homotopy))).

(** Transport a supplied composite both ways through both input chains,
    keeping exactly the same output representative. *)

(** 沿两个输入链双向运输给定合成，保留完全相同的输出代表。 *)

Definition initial_composite
  := CocycleTwoSphereMul first_input.1 second_input.1.

Definition forward_composite
  := fst (two_sphere_composite_class BoolCocycleModel
      (two_cocycle_simplex_unit 0) first_chain second_chain
      (cocycle_two_sphere_mul first_input.1 second_input.1))
      initial_composite.

Definition backward_composite
  := snd (two_sphere_composite_class BoolCocycleModel
      (two_cocycle_simplex_unit 0) first_chain second_chain
      (cocycle_two_sphere_mul first_input.1 second_input.1))
      forward_composite.

(** Inspect every triangular face of each actual tetrahedron. *)

(** 检查每个实际四面体的全部三角形面。 *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺] w),
      two_cocycle_triangle_value_resp (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example binary_transport_computes
  : (face_values first_homotopy.1, face_values second_homotopy.1,
     face_values forward_composite.1, face_values backward_composite.1)
      = ((false, false, true, true), (false, false, true, true),
         (false, true, false, true), (false, true, false, true)).
Proof. vm_compute. reflexivity. Defined.

(** Choose a magma explicitly, with actual Kan three-horn selection. *)

(** 使用实际 Kan 三维 horn 选择，显式选择原群。 *)

Definition three_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Definition class_magma
  : Magma BoolCocycleSphereClassS
  := TwoSphereClassMagma BoolCocycleModel (two_cocycle_simplex_unit 0)
      three_choice.

(** Use the generic product-map construction rather than a new wrapper. *)

(** 使用通用积映射构造，不新增包装。 *)

Definition product_value (a b : bool)
  : bool
  := cocycle_two_sphere_class_value_resp
      (set_magma_mul_resp class_magma
        (cocycle_two_sphere_resp a, cocycle_two_sphere_resp b)).

Example magma_computes
  : (product_value false false, product_value false true,
     product_value true false, product_value true true)
      = (false, true, true, false).
Proof. vm_compute. reflexivity. Defined.

(** The packaged operation retains an actual composite, not just a label. *)

(** 打包运算保留实际合成，不只是标签。 *)

Example chosen_tetrahedron_computes
  : face_values (TwoSphereKanMulComposite BoolCocycleModel
      (two_cocycle_simplex_unit 0) three_choice first_input.1 second_input.1).1
      = (false, true, false, true).
Proof. vm_compute. reflexivity. Defined.

(** Consume the product map's Proper field with both actual input chains. *)

(** 用两条实际输入链消费积映射的 Proper 字段。 *)

Example product_preserves_both_chains
  : set_magma_mul_resp class_magma (first_input.1, second_input.1) ≈S
      set_magma_mul_resp class_magma (first_direct, second_direct).
Proof. apply func_proper. split; [exact first_chain | exact second_chain]. Defined.

(** Arbitrary supplied composites, not merely selected outputs, are
    compared through the same two generated input equalities. *)

(** 任意给定合成均沿同样两个生成输入相等比较，不局限于选定输出。 *)

Example supplied_outputs_agree
  : (cocycle_two_sphere_mul first_input.1 second_input.1
      : BoolCocycleSphereClassS) ≈S
      cocycle_two_sphere_mul first_direct second_direct.
Proof.
  exact (two_sphere_composite_output_class_eq BoolCocycleModel
    (two_cocycle_simplex_unit 0) initial_composite
    (CocycleTwoSphereMul first_direct second_direct) first_chain second_chain).
Defined.
