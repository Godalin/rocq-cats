From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderIso
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Genuinely Nontrivial Base Correction

    The forward map negates boolean representatives; its chosen inverse
    is the identity, valid in the specified Type-valued total relation.
    The inverse image of the image base is true while the source base is
    false. Round trips therefore need actual equality, not native equality.
    Independently selected group operations remain observable. *)

(** * 确实非平凡的基点校正

    正向映射取反布尔代表，所选逆为恒等，在指定 Type 值全关系中确实互逆。
    像基点的逆像是 true，来源基点却是 false。因此往返需要实际相等，不能
    使用原生相等；独立选定群运算仍可观察。 *)

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

(** Negation is respectful in every degree. *)

(** 取反在每一维保相等。 *)

Program Definition flip_resp
  : WitnessS →r WitnessS
  :=
  {|func := negb
  |}.
Next Obligation. intros a c E. exact E. Defined.

(** A constant component is natural for the constant simplicial object. *)

(** 对常值单纯对象，常值分量自然。 *)

Program Definition FlipN
  : W ⇒ W
  :=
  {|nt n := flip_resp
  |}.
Next Obligation. intros a. exact true. Defined.

(** Select the identity inverse, deliberately different from negation. *)

(** 选定恒等逆，刻意区别于取反。 *)

Definition flip_iso
  : FlipN ⦂ W ≅N W.
Proof. intros n. exists id_resp. split; intros a; exact false. Defined.

(** A sphere at the image vertex has its own boundary witnesses. *)

(** 像顶点处的球面具有自己的边界见证。 *)

Definition z
  : TwoSphereS W true
  := (true; λ i, false).

(** Use the original forward map and new corrected inverse. *)

(** 使用原正向映射及新校正逆。 *)

Definition forward
  : Q false false true →r Q true true false
  := two_sphere_cylinder_map_resp FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

Definition backward
  : Q true true false →r Q false false true
  := two_sphere_cylinder_inverse_resp FlipN flip_iso false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

(** The inverse product law uses exactly the selected group parent operations. *)

(** 逆映射乘积律恰好使用选定群父运算。 *)

Definition product_cylinder
  : TwoSphereCylinderHomotopy W false
      (backward (@mul _ (hasMagma (G true true false true)) z z))
      (@mul _ (hasMagma (G false false true false)) (backward z) (backward z))
  := two_sphere_cylinder_inverse_mul FlipN flip_iso false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (one_choice _ _ true) (one_choice _ _ false) z z.

(** Left-candidate preservation consumes the same two inverses. *)

(** 左候选保持消费相同的两个群逆。 *)

Definition inverse_cylinder
  : TwoSphereCylinderHomotopy W false
      (backward (@inv _ (hasGroup (G true true false true)) z))
      (@inv _ (hasGroup (G false false true false)) (backward z))
  := two_sphere_cylinder_inverse_left_inverse FlipN flip_iso false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (one_choice _ _ true) (one_choice _ _ false)
      (one_choice _ _ false) (one_choice _ _ false) z.

(** Unit preservation really corrects true to false. *)

(** 单位保持确实将 true 校正到 false。 *)

Definition unit_cylinder
  : TwoSphereCylinderHomotopy W false
      (backward (@mul_unit _ (hasMonoid (G true true false true))))
      (@mul_unit _ (hasMonoid (G false false true false)))
  := two_sphere_cylinder_inverse_unit FlipN flip_iso false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

(** Both round trips compare the actual original representatives. *)

(** 两种往返比较实际原代表。 *)

Definition left_cylinder
  : TwoSphereCylinderHomotopy W false (backward (forward x)) x
  := two_sphere_cylinder_inverse_l FlipN flip_iso false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) x.

Definition right_cylinder
  : TwoSphereCylinderHomotopy W true (forward (backward z)) z
  := two_sphere_cylinder_inverse_r FlipN flip_iso false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) z.

(** The respectful inverse consumes an actual input cylinder. *)

(** 保相等逆消费实际输入柱。 *)

Definition mapped_input_cylinder
  := @func_proper _ _ backward z (two_sphere_base W true)
      (TwoSphereConstantCylinder W true z (two_sphere_base W true) true).

(** A common-lift isomorphism reuses the original class comparison. *)

(** 共同提升同构复用原类比较。 *)

Definition comparison
  := two_sphere_cylinder_iso FlipN flip_iso false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

(** Read the nontrivial base correction and all native-distinct law endpoints. *)

(** 读取非平凡基点校正及各原生不同的定律端点。 *)

Example base_and_operations_compute
  : ((FlipN ^-1N flip_iso) 0 (FlipN 0 false), false,
     (backward (forward x)).1, x.1,
     (forward (backward z)).1, z.1,
     (backward (@mul _ (hasMagma (G true true false true)) z z)).1,
     (@mul _ (hasMagma (G false false true false)) (backward z) (backward z)).1,
     (backward (@inv _ (hasGroup (G true true false true)) z)).1,
     (@inv _ (hasGroup (G false false true false)) (backward z)).1,
     (backward (@mul_unit _ (hasMonoid (G true true false true)))).1,
     (@mul_unit _ (hasMonoid (G false false true false))).1) =
    (true, false, true, false, false, true, true, false,
     true, false, true, false).
Proof. vm_compute. reflexivity. Defined.

(** Both isomorphism directions retain the expected representative functions. *)

(** 同构两个方向保留预期的代表函数。 *)

Example iso_directions_compute
  : ((lower (comparison.1 {|lower := x|})).1,
     (lower (comparison.2.1 {|lower := z|})).1) = (true, true).
Proof. vm_compute. reflexivity. Defined.

Definition forward_is_same_map (a : Q false false true)
  : lower (comparison.1 {|lower := a|}) = forward a
  := eq_refl.

Definition backward_is_same_map (a : Q true true false)
  : lower (comparison.2.1 {|lower := a|}) = backward a
  := eq_refl.

(** The corrected inverse is also definitionally the old class inverse
    on representatives, including its boundary proof rather than just values. *)

(** 校正逆在代表上也按定义就是原类逆，包括边界证明，不只是值。 *)

Definition backward_is_old_class_map (a : Q true true false)
  : backward a = two_sphere_class_inverse_resp FlipN flip_iso false a
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

(** All five law cylinders and input Proper have full varying-time boundaries. *)

(** 五项定律柱及输入 Proper 均具有完整变化时间边界。 *)

Definition all_six_full_boundaries
  := (product_cylinder.2 5 boundary_space varying_time,
      inverse_cylinder.2 5 boundary_space varying_time,
      unit_cylinder.2 5 boundary_space varying_time,
      left_cylinder.2 5 boundary_space varying_time,
      right_cylinder.2 5 boundary_space varying_time,
      mapped_input_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Specified inverse equations and operation laws do not imply native ones. *)

(** 指定互逆方程及运算定律不蕴含原生方程。 *)

Fail Definition left_not_native
  : backward (forward x) = x
  := ltac:(vm_compute; reflexivity).
Fail Definition right_not_native
  : forward (backward z) = z
  := ltac:(vm_compute; reflexivity).
Fail Definition product_not_native
  : backward (@mul _ (hasMagma (G true true false true)) z z) =
      @mul _ (hasMagma (G false false true false)) (backward z) (backward z)
  := ltac:(vm_compute; reflexivity).
Fail Definition inverse_not_native
  : backward (@inv _ (hasGroup (G true true false true)) z) =
      @inv _ (hasGroup (G false false true false)) (backward z)
  := ltac:(vm_compute; reflexivity).
Fail Definition unit_not_native
  : backward (@mul_unit _ (hasMonoid (G true true false true))) =
      @mul_unit _ (hasMonoid (G false false true false))
  := ltac:(vm_compute; reflexivity).

(** ** Real Nonzero Cocycle Consumers

    The identity natural isomorphism uses the actual Kan fillers, selected
    cylinder group and coefficient decoder. This is a model regression,
    without replacing the corrected inverse or its operation witnesses. *)

(** ** 真实非零 Cocycle 消费者

    恒等自然同构使用实际 Kan 填充、选定柱群及系数读取。这是模型回归，不替换
    校正逆或其运算见证。 *)

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

(** Use the actual corrected inverse of the identity natural isomorphism. *)

(** 使用恒等自然同构的实际校正逆。 *)

Definition model_backward
  : CZ →r CZ
  := two_sphere_cylinder_inverse_resp (IdN : Z ⇒ Z) (nat_id_iso Z) b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺).

(** Decode through the original class comparison, retaining the new map's
    actual output rather than replacing its selected operation. *)

(** 经原类比较读取，保留新映射的实际输出，不替换选定运算。 *)

Definition value
  : CZ →r BoolS
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) ∘r
      two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
        (cocycle_choices fin_first⁺).

(** Coefficients remain those of the actual product and inverse outputs. *)

(** 系数仍为实际乘积与逆输出的系数。 *)

Example nonzero_inverse_map_compute
  : (value (model_backward bool_cocycle_sphere),
     value (model_backward
       (@mul _ (hasMagma GZ) bool_cocycle_sphere bool_cocycle_sphere)),
     value (@mul _ (hasMagma GZ) (model_backward bool_cocycle_sphere)
       (model_backward bool_cocycle_sphere)),
     value (model_backward (@inv _ (hasGroup GZ) bool_cocycle_sphere)),
     value (@inv _ (hasGroup GZ) (model_backward bool_cocycle_sphere))) =
    (true, false, false, true, true).
Proof. vm_compute. reflexivity. Defined.

(** Both operation laws produce actual cylinders in the real Kan model. *)

(** 两项运算定律在真实 Kan 模型中产生实际柱。 *)

Definition cocycle_product_cylinder
  := two_sphere_cylinder_inverse_mul (IdN : Z ⇒ Z) (nat_id_iso Z) b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      product_choice product_choice bool_cocycle_sphere bool_cocycle_sphere.

Definition cocycle_inverse_cylinder
  := two_sphere_cylinder_inverse_left_inverse (IdN : Z ⇒ Z) (nat_id_iso Z) b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      left_choice product_choice left_choice right_choice bool_cocycle_sphere.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

Definition cocycle_full_boundaries
  := (cocycle_product_cylinder.2 5 boundary_space varying_time,
      cocycle_inverse_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** A nonzero actual inverse image still cannot equal the unit by a cylinder. *)

(** 实际非零逆像仍不能由柱等于单位。 *)

Definition inverse_image_nonzero_not_unit
  : ¬ ((model_backward bool_cocycle_sphere : CZ) ≈S @mul_unit _ (hasMonoid GZ)).
Proof.
  intros E. pose proof (@func_proper CZ BoolS value _ _ E) as H.
  change (true = false) in H. discriminate H.
Defined.

(** Even full Kan still does not select Group or raw cylinder Equivalence. *)

(** 即使完整 Kan 仍不选择群或原始柱等价。 *)

Fail Definition full_Kan_no_group : HasMagma CZ := ltac:(typeclasses eauto).
Fail Definition full_Kan_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Z b)
  := ltac:(typeclasses eauto).
