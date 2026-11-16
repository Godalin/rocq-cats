From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderBase
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Native-Distinct Vertices and Independent Witnesses

    In the constant witness setoid, false and true are equal by either
    boolean witness. Base transport keeps triangles. Independently chosen
    source/target group products and inverses can have native-distinct
    outputs; the new laws must still provide actual relative cylinders. *)

(** * 原生不同顶点与独立见证

    在常值见证广集中，false 与 true 可由任一布尔见证相等。基点运输保留三角形；
    独立选定的来源／目标群乘积与逆可有原生不同输出，新定律仍须提供实际相对柱。 *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation. split; red; intros; exact true. Defined.

(** Retain the witness setoid in every degree. *)

(** 在每一维保留该见证广集。 *)

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

(** The original input retains its boundary witnesses. *)

(** 原输入保留自己的边界见证。 *)

Definition x
  : TwoSphereS W false
  := (false; λ i, true).

(** A second native-distinct input has different witnesses. *)

(** 第二个原生不同输入具有不同见证。 *)

Definition y
  : TwoSphereS W false
  := (true; λ i, false).

(** Constant prescribed fillers are genuine choices, not unique or Proper. *)

(** 指定常值填充是真实选择，不要求唯一或 Proper。 *)

Program Definition one_choice (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers W n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m z. exact true. Defined.

(** Independent presentation families need not be carried to each other. *)

(** 独立呈现族不要求经映射对应。 *)

Definition choices (r : Ordinal 2) (v : bool) (s : Ordinal 8)
  : HasHornFillers W (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s)
  := one_choice _ _ v.

(** Supply only the four-dimensional choices used by the actual groups. *)

(** 只提供实际群使用的四维选择。 *)

Local Definition four2
  : HasHornFillers W 4 fin_first⁺⁺
  := one_choice _ _ false.

(** Associativity retains its own choice. *)

(** 结合律保留自己的选择。 *)

Local Definition four3
  : HasHornFillers W 4 fin_first⁺⁺⁺
  := one_choice _ _ true.

(** Input descent retains its other choice. *)

(** 输入下降保留另一选择。 *)

Local Definition four4
  : HasHornFillers W 4 fin_first⁺⁺⁺⁺
  := one_choice _ _ false.

Local Existing Instance four2.
Local Existing Instance four3.
Local Existing Instance four4.

(** The basepoint and the presentation choices are independent parameters. *)

(** 基点和呈现选择是独立参数。 *)

Definition Q (b r c : bool)
  : SetC
  := TwoSphereCylinderS W b (choices fin_first r) (choices fin_first⁺ c).

(** Product and left candidate use the supplied value; the right candidate
    is independently false. No chosen model is registered. *)

(** 乘积和左候选使用给定值，右候选独立为 false；不注册选定模型。 *)

Definition G (b r c v : bool)
  : Group
  := TwoSphereCylinderGroup W b (choices fin_first r) (choices fin_first⁺ c)
      (one_choice _ _ v) (one_choice _ _ v) (one_choice _ _ false).

(** Transport changes the vertex and the presentation, not the triangle. *)

(** 运输改变顶点与呈现，不改变三角形。 *)

Definition moved (E : @carrier_equiv WitnessS false true)
  : Q false false true →r Q true true false
  := two_sphere_cylinder_change_base_resp W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) E.

(** The actual source and target groups retain different selections. *)

(** 实际来源及目标群保留不同选择。 *)

Definition product_cylinder
  : TwoSphereCylinderHomotopy W true
      (moved true (@mul _ (hasMagma (G false false true false)) x y))
      (@mul _ (hasMagma (G true true false true)) (moved true x) (moved true y))
  := two_sphere_cylinder_change_base_mul W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) true
      (one_choice _ _ false) (one_choice _ _ true) x y.

(** Left inverse preservation uses those same selected group operations. *)

(** 左逆保持使用完全相同的选定群运算。 *)

Definition inverse_cylinder
  : TwoSphereCylinderHomotopy W true
      (moved false (@inv _ (hasGroup (G false false true false)) x))
      (@inv _ (hasGroup (G true true false true)) (moved false x))
  := two_sphere_cylinder_change_base_left_inverse W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) false
      (one_choice _ _ false) (one_choice _ _ true)
      (one_choice _ _ true) (one_choice _ _ false) x.

(** Units use the native-distinct specified equal vertices. *)

(** 单位使用原生不同但指定相等的顶点。 *)

Definition unit_cylinder
  : TwoSphereCylinderHomotopy W true
      (moved true (@monoid_unit _ (hasMonoid (G false false true false))))
      (@monoid_unit _ (hasMonoid (G true true false true)))
  := @two_sphere_cylinder_change_base_unit W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) false true true.

(** Equality witnesses remain different boolean data. *)

(** 相等见证保持为不同布尔数据。 *)

Definition witness_cylinder
  := @two_sphere_cylinder_change_base_witness W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) false true true false y.

(** Identity uses its original presentation. *)

(** 恒等使用原呈现。 *)

Definition identity_cylinder
  := two_sphere_cylinder_change_base_id W
      (choices fin_first false) (choices fin_first⁺ true) false y.

(** Two transports retain an independent intermediate presentation. *)

(** 两次运输保留独立中间呈现。 *)

Definition composition_cylinder
  := @two_sphere_cylinder_change_base_comp W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (choices fin_first false) (choices fin_first⁺ false)
      false true false true false y.

(** Map an actual input cylinder using the new respectful map. *)

(** 用新保相等映射映射一份实际输入柱。 *)

Definition mapped_input_cylinder
  := @func_proper _ _ (moved false) x y
      (TwoSphereConstantCylinder W false x y true).

(** The old generic composite isomorphism supplies both directions. *)

(** 原通用复合同构提供两个方向。 *)

Definition comparison
  := @two_sphere_cylinder_change_base_iso W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) false true true.

(** Evaluate retained triangles and the actual distinct endpoints of product/inverse/unit preservation. *)

(** 求值保留三角形及乘积／逆／单位保持的实际不同端点。 *)

Example transport_and_operations_compute
  : ((moved true y).1, (moved false y).1,
     (moved true (@mul _ (hasMagma (G false false true false)) x y)).1,
     (@mul _ (hasMagma (G true true false true)) (moved true x) (moved true y)).1,
     (moved false (@inv _ (hasGroup (G false false true false)) x)).1,
     (@inv _ (hasGroup (G true true false true)) (moved false x)).1,
     (moved true (@monoid_unit _ (hasMonoid (G false false true false)))).1,
     (@monoid_unit _ (hasMonoid (G true true false true))).1) =
    (true, true, false, true, false, true, false, true).
Proof. vm_compute. reflexivity. Defined.

(** Both directions use precisely the raw base-change representative. *)

(** 两个方向恰好使用原始换基代表。 *)

Example comparison_directions_compute
  : ((lower (comparison.1 {|lower := x|})).1,
     (lower (comparison.2.1 {|lower := moved false y|})).1) = (false, true).
Proof. vm_compute. reflexivity. Defined.

Definition forward_is_same_map (a : Q false false true)
  : lower (comparison.1 {|lower := a|}) = moved true a
  := eq_refl.

Definition backward_is_same_map (a : Q true true false)
  : lower (comparison.2.1 {|lower := a|}) =
      two_sphere_change_base_resp W (symmetry (true :
        @carrier_equiv WitnessS false true)) a
  := eq_refl.

(** A boundary shape is independent of its varying time coordinate. *)

(** 边界形状独立于其变化的时间坐标。 *)

Definition boundary_space
  : (∂Δ[2]) 5
  := {|lower := (δ[1; fin_first⁺] ∘
        SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4);
      sieve_precomp (BoundarySieve 2) δ[1; fin_first⁺]
        (SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4))
        (boundary_face_member fin_first⁺))|}.

(** Time varies through a separate simplex operator. *)

(** 时间通过另一个单形算子变化。 *)

Definition varying_time
  : (Δ[1]) 5
  := {|lower := SimplexPrismTimeF (fin_first⁺ : Ordinal 4)|}.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Every new pointwise law retains the complete relative boundary. *)

(** 每项新逐点定律都保留完整相对边界。 *)

Definition all_seven_full_boundaries
  := (product_cylinder.2 5 boundary_space varying_time,
      inverse_cylinder.2 5 boundary_space varying_time,
      unit_cylinder.2 5 boundary_space varying_time,
      witness_cylinder.2 5 boundary_space varying_time,
      identity_cylinder.2 5 boundary_space varying_time,
      composition_cylinder.2 5 boundary_space varying_time,
      mapped_input_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Actual-cylinder equations do not imply native endpoint equality. *)

(** 实际柱方程不蕴含原生端点相等。 *)

Fail Definition product_not_native
  : moved true (@mul _ (hasMagma (G false false true false)) x y) =
      @mul _ (hasMagma (G true true false true)) (moved true x) (moved true y)
  := ltac:(vm_compute; reflexivity).
Fail Definition inverse_not_native
  : moved false (@inv _ (hasGroup (G false false true false)) x) =
      @inv _ (hasGroup (G true true false true)) (moved false x)
  := ltac:(vm_compute; reflexivity).
Fail Definition unit_not_native
  : moved true (@monoid_unit _ (hasMonoid (G false false true false))) =
      @monoid_unit _ (hasMonoid (G true true false true))
  := ltac:(vm_compute; reflexivity).

(** ** The Actual Nonzero Cocycle Sphere

    Reuse the real Kan choices and coefficient decoder. Reflexive base
    transport still consumes the new construction, preserves the nonzero
    sphere and supplies actual cylinders for the same group operations. *)

(** ** 实际非零 Cocycle 球面

    复用真实 Kan 选择与系数读取。自反基点运输仍消费新构造，保留非零球面，
    并为同一群运算提供实际柱。 *)

Local Existing Instance BoolCocycleModel_HasKanFillers.

Definition Z
  : Fct (Δ^op) SetCat
  := BoolCocycleModel.

(** Keep the original unit basepoint. *)

(** 保持原单位基点。 *)

Definition b
  : Z 0
  := (two_cocycle_simplex_unit (M := BoolS_Monoid)) 0.

(** Select the actual model's presentation fillers explicitly. *)

(** 显式选择实际模型的呈现填充。 *)

Definition cocycle_choices (r : Ordinal 2) (s : Ordinal 8)
  := @hasHornFillers Z BoolCocycleModel_HasKanFillers
      (simplex_triangle_horn_face_dim s) (simplex_triangle_horn_missing r s).

(** The target equality remains actual full relative cylinders. *)

(** 目标相等仍为实际完整相对柱。 *)

Definition CZ
  : SetC
  := TwoSphereCylinderS Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺).

(** Supply the actual product choice. *)

(** 提供实际乘法选择。 *)

Definition product_choice
  : HasHornFillers Z 3 fin_first⁺⁺
  := _.

(** Supply the actual left-candidate choice separately. *)

(** 单独提供实际左候选选择。 *)

Definition left_choice
  : HasHornFillers Z 3 fin_first⁺⁺⁺
  := _.

(** The right choice remains a separate argument. *)

(** 右选择保持为单独参数。 *)

Definition right_choice
  : HasHornFillers Z 3 fin_first⁺
  := _.

(** Choose the exact same original cylinder group. *)

(** 选择完全相同的原柱群。 *)

Definition GZ
  : Group
  := TwoSphereCylinderGroup Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺) product_choice left_choice right_choice.

(** Reflexive transport uses the new cylinder base map. *)

(** 自反运输使用新的柱基点映射。 *)

Definition model_mapped
  : CZ →r CZ
  := two_sphere_cylinder_change_base_resp Z
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺) (reflexivity b).

(** Decode through the original class comparison, retaining the new map's
    actual output rather than replacing its selected operation. *)

(** 经原类比较读取，保留新映射的实际输出，不替换选定运算。 *)

Definition value
  : CZ →r BoolS
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) ∘r
      two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
        (cocycle_choices fin_first⁺).

(** Nonzero transport and its inverse have the expected coefficients. *)

(** 非零运输及其逆具有预期系数。 *)

Example nonzero_transport_compute
  : (value (model_mapped bool_cocycle_sphere),
     value (model_mapped (@inv _ (hasGroup GZ) bool_cocycle_sphere)),
     value (@inv _ (hasGroup GZ) (model_mapped bool_cocycle_sphere))) =
    (true, true, true).
Proof. vm_compute. reflexivity. Defined.

(** The new inverse law is an actual cocycle cylinder. *)

(** 新逆定律是实际 cocycle 柱。 *)

Definition cocycle_inverse_cylinder
  := two_sphere_cylinder_change_base_left_inverse Z
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (reflexivity b) left_choice product_choice left_choice right_choice
      bool_cocycle_sphere.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

Definition cocycle_full_boundary
  := cocycle_inverse_cylinder.2 5 boundary_space varying_time.

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** The transported actual nonzero sphere is still not the unit. *)

(** 运输后的实际非零球面仍不等于单位。 *)

Definition transported_nonzero_not_unit
  : ¬ ((model_mapped bool_cocycle_sphere : CZ) ≈S @monoid_unit _ (hasMonoid GZ)).
Proof.
  intros E. pose proof (@func_proper CZ BoolS value _ _ E) as H.
  change (true = false) in H. discriminate H.
Defined.

(** Full Kan still does not enable a group or raw cylinder equivalence. *)

(** 完整 Kan 仍不启用群或原始柱等价。 *)

Fail Definition full_Kan_no_group : HasMagma CZ := ltac:(typeclasses eauto).
Fail Definition full_Kan_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Z b)
  := ltac:(typeclasses eauto).
