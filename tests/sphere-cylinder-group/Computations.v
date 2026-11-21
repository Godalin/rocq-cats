From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderGroup
  Instance.Set.Simplicial.Cocycle.SphereKanGroup
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Computation and Actual Relative-Cylinder Group Laws

    First use a model whose equality has Boolean witnesses and native-distinct
    representatives. Independently chosen presentation/algebra fillers expose
    the exact selected product and left inverse. Then test the actual nonzero
    Boolean cocycle model; coefficient decoding remains a client, not the
    definition of the transported operations. *)

(** * 计算与实际相对柱群律

    先用具有布尔相等见证和原生不同代表的模型，独立呈现／代数填充暴露实际选定
    乘积和左逆；再检查实际非零布尔 cocycle 模型。系数读取仅为消费者，不定义
    运输后的运算。 *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation. split; red; intros; exact true. Defined.

(** A constant simplicial setoid with genuine Type-valued equality data. *)

(** 具有真实 Type 值相等数据的常值单纯广集。 *)

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

(** Two native-distinct representatives also retain different boundaries. *)

(** 两个原生不同代表还保留不同的边界见证。 *)

Definition x
  : TwoSphereS W false
  := (false; λ i, true).

(** The second triangle keeps its own boundary witnesses. *)

(** 第二个三角形保留自己的边界见证。 *)

Definition y
  : TwoSphereS W false
  := (true; λ i, false).

(** The actual filler returns a supplied Boolean, with no uniqueness law. *)

(** 实际填充返回给定布尔值，不要求唯一性。 *)

Program Definition one_choice (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers W n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m h'. exact true. Defined.

(** Only presentation equivalence uses these nine-choice families. *)

(** 只有呈现等价使用这些九选择族。 *)

Definition choices (r : Ordinal 2) (v : bool) (s : Ordinal 8)
  : HasHornFillers W (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s)
  := one_choice _ _ v.

(** Enable exactly the old four-dimensional algebra choices locally. *)

(** 局部启用恰好原有的四维代数选择。 *)

Local Definition four2
  : HasHornFillers W 4 fin_first⁺⁺
  := one_choice _ _ false.

(** Associativity's choice remains independent. *)

(** 结合律选择保持独立。 *)

Local Definition four3
  : HasHornFillers W 4 fin_first⁺⁺⁺
  := one_choice _ _ true.

(** Input transport's other choice is supplied separately. *)

(** 输入运输的另一选择单独给出。 *)

Local Definition four4
  : HasHornFillers W 4 fin_first⁺⁺⁺⁺
  := one_choice _ _ false.

Local Existing Instance four2.
Local Existing Instance four3.
Local Existing Instance four4.

(** Presentation choices may vary without changing representative operations. *)

(** 呈现选择可变化，而不改变代表运算。 *)

Definition Q (r c : bool)
  : SetC
  := TwoSphereCylinderS W false (choices fin_first r) (choices fin_first⁺ c).

(** Multiplication, left and right inverse selections are three independent
    data: true, false and true respectively. No instance is exported. *)

(** 乘法、左右逆选择分别是独立数据 true、false、true，不导出实例。 *)

Definition G (r c : bool)
  : Group
  := TwoSphereCylinderGroup W false
      (choices fin_first r) (choices fin_first⁺ c)
      (one_choice _ _ true) (one_choice _ _ false) (one_choice _ _ true).

(** Compute through the full selected parent chain, not a replacement formula. *)

(** 经完整选定父链计算，不替换成另一公式。 *)

Example selected_operations_compute
  : ((@mul _ (hasMagma (G false true)) x y).1,
     (@mul _ (hasMagma (G false true)) y x).1,
     (@mul_unit _ _ (hasUnit (G false true))).1,
     (@inv _ _ _ (hasInverse (G false true)) x).1,
     (@inv _ _ _ (hasInverse (G false true)) y).1) =
    (true, true, false, false, false).
Proof. vm_compute. reflexivity. Defined.

(** Changing only presentation choices leaves the full selected output
    representative definitionally unchanged, including its boundary data. *)

(** 只改变呈现选择时，整个选定输出代表按定义不变，包括其边界数据。 *)

Example presentation_choices_keep_values
  : ((@mul _ (hasMagma (G false true)) x y : TwoSphereS W false),
     (@mul_unit _ _ (hasUnit (G false true)) : TwoSphereS W false),
     (@inv _ _ _ (hasInverse (G false true)) y : TwoSphereS W false)) =
    ((@mul _ (hasMagma (G true false)) x y : TwoSphereS W false),
     (@mul_unit _ _ (hasUnit (G true false)) : TwoSphereS W false),
     (@inv _ _ _ (hasInverse (G true false)) y : TwoSphereS W false)).
Proof. vm_compute. reflexivity. Defined.

(** Recovery preserves the original triangle and its native boundary witness. *)

(** 恢复保留原三角形及其原生边界见证。 *)

Example recovery_keeps_representative
  : ((two_sphere_cylinder_of_class_resp W false
        (choices fin_first false) (choices fin_first⁺ true)
        (two_sphere_class_of_cylinder_resp W false
          (choices fin_first false) (choices fin_first⁺ true) y)).1,
     y.2 fin_first) = (true, false).
Proof. vm_compute. reflexivity. Defined.

(** A genuinely non-native input equality is an actual relative cylinder. *)

(** 真实非原生输入相等是一份实际相对柱。 *)

Definition input_cylinder
  : TwoSphereCylinderHomotopy W false x y
  := TwoSphereConstantCylinder W false x y true.

(** Generic inverse Proper consumes that actual cylinder. *)

(** 通用逆 Proper 消费该实际柱。 *)

Definition inverse_cylinder
  : TwoSphereCylinderHomotopy W false
      (@inv _ _ _ (hasInverse (G false true)) x)
      (@inv _ _ _ (hasInverse (G false true)) y)
  := @inv_proper _ _ (@isInverse _ _ _ (hasInverse (G false true))) x y input_cylinder.

(** Generic left unit returns a cylinder between native-distinct values. *)

(** 通用左单位返回原生不同值之间的柱。 *)

Definition left_unit_cylinder
  : TwoSphereCylinderHomotopy W false
      (@mul _ (hasMagma (G false true))
        (@mul_unit _ _ (hasUnit (G false true))) x) x
  := @mul_unit_l _ _ _ (@isUnit _ _ (hasUnit (G false true))) x.

(** The right-unit law is the inherited law of that same monoid. *)

(** 右单位律是同一幺半群的继承定律。 *)

Definition right_unit_cylinder
  : TwoSphereCylinderHomotopy W false
      (@mul _ (hasMagma (G false true)) y
        (@mul_unit _ _ (hasUnit (G false true)))) y
  := @mul_unit_r _ _ _ (@isUnit _ _ (hasUnit (G false true))) y.

(** Both inverse equations return actual cylinders, including the independently
    chosen right-candidate comparison already proved in the source group. *)

(** 两个逆方程都返回实际柱，包括来源群已证的独立右候选比较。 *)

Definition left_inverse_cylinder
  := @mul_inv_l _ _ _ _ (@isInverse _ _ _ (hasInverse (G false true))) y.

(** Read the right law from the same selected group. *)

(** 从同一选定群读取右律。 *)

Definition right_inverse_cylinder
  := @mul_inv_r _ _ _ _ (@isInverse _ _ _ (hasInverse (G false true))) y.

(** The actual associativity law is obtained from its same inherited parent. *)

(** 实际结合律来自其同一继承父结构。 *)

Definition associative_cylinder
  := @mul_assoc _ _ (isSemigroup (G false true)) x y x.

(** Generic involution and uniqueness require no sphere-specific proofs. *)

(** 通用对合及唯一性不要求球面专门证明。 *)

Definition involution_cylinder
  := @inv_inv (G false true) y.

(** Use the actual left-inverse cylinder as input to generic uniqueness. *)

(** 用实际左逆柱作为通用唯一性的输入。 *)

Definition uniqueness_cylinder
  := @inv_unique (G false true) y
      (@inv _ _ _ (hasInverse (G false true)) y) left_inverse_cylinder.

(** A five-dimensional boundary shape and independently varying time exercise
    the entire relative law, rather than just its vertices. *)

(** 五维边界形状及独立变化的时间检查完整相对律，而非只检查顶点。 *)

Definition boundary_space
  : (∂Δ[2]) 5
  := {|lower := (δ[1; fin_first⁺] ∘
        SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4);
      sieve_precomp (BoundarySieve 2) δ[1; fin_first⁺]
        (SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4))
        (boundary_face_member fin_first⁺))|}.

(** Time varies along a different simplex operator. *)

(** 时间沿另一单形算子变化。 *)

Definition varying_time
  : (Δ[1]) 5
  := {|lower := SimplexPrismTimeF (fin_first⁺ : Ordinal 4)|}.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** All eight actual laws retain their full boundary proofs. *)

(** 八份实际定律均保留完整边界证明。 *)

Definition complete_boundary_clients
  := (inverse_cylinder.2 5 boundary_space varying_time,
      left_unit_cylinder.2 5 boundary_space varying_time,
      right_unit_cylinder.2 5 boundary_space varying_time,
      left_inverse_cylinder.2 5 boundary_space varying_time,
      right_inverse_cylinder.2 5 boundary_space varying_time,
      associative_cylinder.2 5 boundary_space varying_time,
      involution_cylinder.2 5 boundary_space varying_time,
      uniqueness_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** A group law is specified cylinder equality, not native triangle equality. *)

(** 群律是指定柱相等，不是原生三角形相等。 *)

Fail Definition unit_law_is_not_native
  : @mul _ (hasMagma (G false true))
      (@mul_unit _ _ (hasUnit (G false true))) x = x
  := eq_refl.
Fail Definition unchosen_model : HasMagma (Q false true)
  := ltac:(typeclasses eauto).
Fail Definition unchosen_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy W false)
  := ltac:(typeclasses eauto).

(** ** The Actual Nonzero Cocycle Model

    Supply the old Boolean model and Kan choices explicitly. Decode actual
    transported group operations and consume the actual cylinder laws;
    none of this identifies general π₂ or general Kan commutativity. *)

(** ** 实际非零 Cocycle 模型

    显式提供既有布尔模型及 Kan 选择，读取实际运输群运算并消费实际柱定律；
    不识别一般 π₂ 或一般 Kan 交换性。 *)

Local Existing Instance BoolCocycleModel_HasKanFillers.

Definition Z
  : Fct (Δ^op) SetCat
  := BoolCocycleModel.

(** The base is the model's original unit vertex. *)

(** 基点为模型原单位顶点。 *)

Definition b
  : Z 0
  := (two_cocycle_simplex_unit (M := BoolS_Monoid)) 0.

(** Select the same actual model fillers for presentation equivalence. *)

(** 为呈现等价选择同一实际模型填充。 *)

Definition cocycle_choices (r : Ordinal 2) (s : Ordinal 8)
  := @hasHornFillers Z BoolCocycleModel_HasKanFillers
      (simplex_triangle_horn_face_dim s) (simplex_triangle_horn_missing r s).

(** The cylinder setoid retains actual full relative homotopies as equality. *)

(** 柱广集仍以实际完整相对同伦为相等。 *)

Definition CZ
  : SetC
  := TwoSphereCylinderS Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺).

(** Multiplication uses the old three-dimensional missing-face-two choice. *)

(** 乘法使用原三维缺第二面选择。 *)

Definition product_choice
  : HasHornFillers Z 3 fin_first⁺⁺
  := _.

(** The actual left-candidate choice remains independently supplied. *)

(** 实际左候选选择仍独立给出。 *)

Definition left_choice
  : HasHornFillers Z 3 fin_first⁺⁺⁺
  := _.

(** The right-candidate choice also remains explicit. *)

(** 右候选选择也保持显式。 *)

Definition right_choice
  : HasHornFillers Z 3 fin_first⁺
  := _.

(** Select the transported group explicitly after all model choices. *)

(** 在全部模型选择之后显式选取运输群。 *)

Definition GZ
  : Group
  := TwoSphereCylinderGroup Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺) product_choice left_choice right_choice.

(** Decode through the original class comparison and coefficient map. *)

(** 经原类比较及系数映射读取。 *)

Definition value
  : CZ →r BoolS
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) ∘r
      two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
        (cocycle_choices fin_first⁺).

(** Actual products still read the xor of coefficients. *)

(** 实际乘积仍读作系数异或。 *)

Definition product_value (a c : bool)
  : bool
  := value (@mul _ (hasMagma GZ) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) c)).

(** Actual selected inverses retain their coefficient values. *)

(** 实际选定逆保留其系数值。 *)

Definition inverse_value (a : bool)
  : bool
  := value (@inv _ _ _ (hasInverse GZ) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)).

Example cocycle_group_computes
  : (product_value false false, product_value false true,
     product_value true false, product_value true true,
     value (@mul_unit _ _ (hasUnit GZ)), inverse_value false, inverse_value true) =
    (false, true, true, false, false, false, true).
Proof. vm_compute. reflexivity. Defined.

(** Coefficient multiplication preservation reuses the old Kan comparison. *)

(** 系数乘法保持复用原 Kan 比较。 *)

Definition value_product_client (a c : CZ)
  : value (@mul _ (hasMagma GZ) a c) ≈S
      @mul _ (hasMagma BoolS_Group) (value a) (value c)
  := cocycle_kan_mul_value product_choice a c.

(** Inverse preservation reuses the old actual left-candidate comparison. *)

(** 逆保持复用原实际左候选比较。 *)

Definition value_inverse_client (a : CZ)
  : value (@inv _ _ _ (hasInverse GZ) a) ≈S
      @inv _ _ _ (hasInverse BoolS_Group) (value a)
  := @cocycle_kan_left_inverse_value BoolS_Group left_choice a.

(** A genuine nonzero sphere is not equal to the unit even by an actual
    cylinder; use the accepted comparison to the original nonzero theorem. *)

(** 真实非零球面即使按实际柱也不等于单位；经已接收比较复用原非零定理。 *)

Definition geometric_nonzero_not_unit
  : ¬ ((bool_cocycle_sphere : CZ) ≈S @mul_unit _ _ (hasUnit GZ)).
Proof.
  intros H. apply bool_cocycle_sphere_not_null.
  exact (@func_proper _ _
    (two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺)) _ _ H).
Defined.

(** A real generic left-inverse law supplies the full cocycle cylinder. *)

(** 实际通用左逆律提供完整 cocycle 柱。 *)

Definition cocycle_inverse_cylinder
  : TwoSphereCylinderHomotopy Z b
      (@mul _ (hasMagma GZ) (@inv _ _ _ (hasInverse GZ) bool_cocycle_sphere)
        bool_cocycle_sphere) (@mul_unit _ _ (hasUnit GZ))
  := @mul_inv_l _ _ _ _ (@isInverse _ _ _ (hasInverse GZ)) bool_cocycle_sphere.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Its full boundary proof is usable at an independently varying time. *)

(** 其完整边界证明可在独立变化的时间处使用。 *)

Definition cocycle_inverse_full_boundary
  := cocycle_inverse_cylinder.2 5 boundary_space varying_time.

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Even explicitly enabled full Kan still selects no cylinder Group,
    commutativity property or raw directed-cylinder Equivalence. *)

(** 即使显式启用完整 Kan，仍不选择柱群、交换性质或原始有向柱等价结构。 *)

Fail Definition full_Kan_no_group : HasMagma CZ := ltac:(typeclasses eauto).
Fail Definition full_Kan_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Z b)
  := ltac:(typeclasses eauto).
