From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderGroupMap
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Map Which Does Not Preserve the Selected Fillers

    Boolean equality witnesses allow native-distinct triangles. Negation
    changes every chosen true filler to false, while the target independently
    selects true again. Product/inverse squares therefore commute by actual
    cylinders, even though their endpoints are not native-equal triangles. *)

(** * 不保持选定填充的映射

    布尔相等见证允许原生不同的三角形。取非将每个选定 true 填充变为 false，
    目标却独立再选 true。因此乘积／逆方块通过实际柱交换，而端点并非原生相等
    的三角形。 *)

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

(** Negation is respectful in the specified Type-valued relation. *)

(** 取非在指定 Type 值关系下保相等。 *)

Program Definition flip_resp
  : WitnessS →r WitnessS
  :=
  {|func := negb
  |}.
Next Obligation. intros a c E. exact E. Defined.

(** The same map is natural in every degree. *)

(** 同一映射在每一维自然。 *)

Program Definition FlipN
  : W ⇒ W
  :=
  {|nt n := flip_resp
  |}.
Next Obligation. intros a. exact true. Defined.

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

(** Both product and left candidate choose true; the right candidate is
    independently false. No chosen model is registered. *)

(** 乘积和左候选都选择 true，右候选独立为 false；不注册选定模型。 *)

Definition G (b r c : bool)
  : Group
  := TwoSphereCylinderGroup W b (choices fin_first r) (choices fin_first⁺ c)
      (one_choice _ _ true) (one_choice _ _ true) (one_choice _ _ false).

(** This is exactly the pre-existing cylinder map, at the negated basepoint. *)

(** 这完全是既有柱映射，基点按取非变化。 *)

Definition mapped
  : Q false false true →r Q true true false
  := two_sphere_cylinder_map_resp FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

(** The two sides of the product and inverse squares really differ natively. *)

(** 乘积及逆方块的两侧确实原生不同。 *)

Example operation_square_endpoints_compute
  : ((mapped (@magma_mul _ (hasMagma (G false false true)) x y)).1,
     (@magma_mul _ (hasMagma (G true true false))
       (mapped x) (mapped y)).1,
     (mapped (@group_inv _ (hasGroup (G false false true)) x)).1,
     (@group_inv _ (hasGroup (G true true false)) (mapped x)).1,
     (mapped (@monoid_unit _ (hasMonoid (G false false true)))).1,
     (@monoid_unit _ (hasMonoid (G true true false))).1) =
    (false, true, false, true, true, true).
Proof. vm_compute. reflexivity. Defined.

(** The product law consumes the exact selected parent operations. *)

(** 乘积律消费完全相同的选定父运算。 *)

Definition product_cylinder
  : TwoSphereCylinderHomotopy W true
      (mapped (@magma_mul _ (hasMagma (G false false true)) x y))
      (@magma_mul _ (hasMagma (G true true false)) (mapped x) (mapped y))
  := two_sphere_cylinder_map_mul FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (one_choice _ _ true) (one_choice _ _ true) x y.

(** Inverse preservation compares the two actual selected group inverses. *)

(** 逆保持比较两个实际选定群逆。 *)

Definition inverse_cylinder
  : TwoSphereCylinderHomotopy W true
      (mapped (@group_inv _ (hasGroup (G false false true)) x))
      (@group_inv _ (hasGroup (G true true false)) (mapped x))
  := two_sphere_cylinder_map_left_inverse FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (one_choice _ _ true) (one_choice _ _ true)
      (one_choice _ _ true) (one_choice _ _ false) x.

(** Unit preservation consumes the units of those same groups. *)

(** 单位保持消费相同群的单位。 *)

Definition unit_cylinder
  : TwoSphereCylinderHomotopy W true
      (mapped (@monoid_unit _ (hasMonoid (G false false true))))
      (@monoid_unit _ (hasMonoid (G true true false)))
  := two_sphere_cylinder_map_unit FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

(** Identity acts on the exact original presentation. *)

(** 恒等作用于完全相同的原呈现。 *)

Definition identity_cylinder
  := two_sphere_cylinder_map_id W false
      (choices fin_first false) (choices fin_first⁺ true) y.

(** Composition retains independent intermediate and final choices. *)

(** 复合保留独立的中间及最终选择。 *)

Definition composition_cylinder
  := two_sphere_cylinder_map_comp
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (choices fin_first false) (choices fin_first⁺ false)
      FlipN FlipN false y.

(** Check actual image values and both composite map definitions. *)

(** 检查实际像值及两份复合映射定义。 *)

Example image_and_composition_compute
  : ((mapped x).1, (mapped y).1,
     (two_sphere_cylinder_map_resp (FlipN ∘Nv FlipN) false
       (choices fin_first false) (choices fin_first⁺ true)
       (choices fin_first false) (choices fin_first⁺ false) y).1,
     (two_sphere_cylinder_map_resp FlipN true
       (choices fin_first true) (choices fin_first⁺ false)
       (choices fin_first false) (choices fin_first⁺ false) (mapped y)).1) =
    (true, false, true, true).
Proof. vm_compute. reflexivity. Defined.

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

(** Every new law supplies the actual complete relative boundary. *)

(** 每项新定律都提供实际完整相对边界。 *)

Definition all_five_full_boundaries
  := (product_cylinder.2 5 boundary_space varying_time,
      inverse_cylinder.2 5 boundary_space varying_time,
      unit_cylinder.2 5 boundary_space varying_time,
      identity_cylinder.2 5 boundary_space varying_time,
      composition_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** The actual witnesses do not imply native endpoint equality. *)

(** 实际见证不蕴含原生端点相等。 *)

Fail Definition product_square_is_not_native
  : mapped (@magma_mul _ (hasMagma (G false false true)) x y) =
      @magma_mul _ (hasMagma (G true true false)) (mapped x) (mapped y)
  := ltac:(vm_compute; reflexivity).
Fail Definition inverse_square_is_not_native
  : mapped (@group_inv _ (hasGroup (G false false true)) x) =
      @group_inv _ (hasGroup (G true true false)) (mapped x)
  := ltac:(vm_compute; reflexivity).

(** ** Mapping the Actual Nonzero Cocycle Group

    The identity simplicial map still consumes the real model fillers and
    actual selected group operations. The nonzero inverse remains nonzero;
    only the usual xor product of the two nonzero elements is the unit. *)

(** ** 映射实际非零 Cocycle 群

    恒等单纯映射仍消费真实模型填充及实际选定群运算。非零元素的逆仍非零，
    只有两个非零元素的异或乘积成为单位。 *)

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

(** The actual map is the old cylinder-map construction. *)

(** 实际映射是原柱映射构造。 *)

Definition model_mapped
  : CZ →r CZ
  := two_sphere_cylinder_map_resp (idN : Z ⇒ Z) b
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

(** Both sides of each square have their actual expected coefficients. *)

(** 每个方块的两侧都具有实际预期系数。 *)

Example nonzero_map_squares_compute
  : (value (model_mapped
       (@magma_mul _ (hasMagma GZ) bool_cocycle_sphere bool_cocycle_sphere)),
     value (@magma_mul _ (hasMagma GZ) (model_mapped bool_cocycle_sphere)
       (model_mapped bool_cocycle_sphere)),
     value (model_mapped (@group_inv _ (hasGroup GZ) bool_cocycle_sphere)),
     value (@group_inv _ (hasGroup GZ) (model_mapped bool_cocycle_sphere)),
     value (model_mapped (@monoid_unit _ (hasMonoid GZ))),
     value (@monoid_unit _ (hasMonoid GZ))) = (false, false, true, true, false, false).
Proof. vm_compute. reflexivity. Defined.

(** The mapped product square is a real cocycle cylinder. *)

(** 像乘积方块是一份真实 cocycle 柱。 *)

Definition cocycle_product_cylinder
  := two_sphere_cylinder_map_mul (idN : Z ⇒ Z) b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      product_choice product_choice bool_cocycle_sphere bool_cocycle_sphere.

(** Its mapped inverse square is also a real cylinder. *)

(** 其像逆方块也是真实柱。 *)

Definition cocycle_inverse_cylinder
  := two_sphere_cylinder_map_left_inverse (idN : Z ⇒ Z) b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      left_choice product_choice left_choice right_choice bool_cocycle_sphere.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Both model witnesses retain the full varying-time relative boundary. *)

(** 两份模型见证都保留完整变化时间的相对边界。 *)

Definition cocycle_full_boundaries
  := (cocycle_product_cylinder.2 5 boundary_space varying_time,
      cocycle_inverse_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** The actual nonzero image still cannot be the group unit by a cylinder. *)

(** 实际非零像仍不能通过柱等于群单位。 *)

Definition mapped_nonzero_not_unit
  : ¬ ((model_mapped bool_cocycle_sphere : CZ) ≈S @monoid_unit _ (hasMonoid GZ)).
Proof.
  intros E. pose proof (@func_proper CZ BoolS value _ _ E) as H.
  change (true = false) in H. discriminate H.
Defined.

(** Full Kan enabling still registers neither a group nor raw equivalence. *)

(** 启用完整 Kan 仍不注册群或原始等价。 *)

Fail Definition full_Kan_no_group : HasMagma CZ := ltac:(typeclasses eauto).
Fail Definition full_Kan_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Z b)
  := ltac:(typeclasses eauto).
