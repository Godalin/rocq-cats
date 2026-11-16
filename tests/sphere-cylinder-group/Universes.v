From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

Local Opaque TwoSphereCylinderEquivalence TwoSphereClassCylinder
  two_sphere_cylinder_class_iff.

(** * Native Sizes, Explicit Choices and the Same Algebra

    The native simplex carrier/equality bounds are strictly ordered both
    ways. Presentation choices are independent of all class-algebra choices.
    No full Kan or model instance is required. *)

(** * 原生大小、显式选择及相同代数

    两种原生单形载体／相等大小次序均严格；呈现选择独立于全部类代数选择。
    不要求完整 Kan 或模型实例。 *)

(** ** Lower Native Equality

    Fix the basepoint, two nine-choice families and exactly the old
    three four-horn choices. Native computations below compare only values
    and immediate parents, never structure-law records. *)

(** ** Lower 原生相等

    固定基点、两组九选择及原有三个四维 horn 选择。下列原生计算仅比较值和
    直接父结构，不比较定律记录。 *)

Section Lower.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}.
Context (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺).

Let C
  : SetC
  := TwoSphereCylinderS X b KR KC.

(** All four structures retain native-sized representatives. *)

(** 四层结构都保留原生大小的代表。 *)

Definition lower_magma
  : Magma
  := TwoSphereCylinderMagma X b KR KC H.

(** Associativity uses the transported magma. *)

(** 结合律使用运输的原群。 *)

Definition lower_semigroup
  : Semigroup
  := TwoSphereCylinderSemigroup X b KR KC H.

(** Unit laws use the same transported semigroup. *)

(** 单位律使用相同运输半群。 *)

Definition lower_monoid
  : Monoid
  := TwoSphereCylinderMonoid X b KR KC H.

(** Inverse laws use the same transported monoid. *)

(** 逆律使用相同运输幺半群。 *)

Definition lower_group
  : Group
  := TwoSphereCylinderGroup X b KR KC H K L.

(** Each immediate parent is retained by native conversion. *)

(** 每个直接父结构按原生定义转换保留。 *)

Definition lower_group_parent
  : GroupToMonoid lower_group = lower_monoid
  := eq_refl.

(** The monoid stores that exact semigroup. *)

(** 幺半群保存完全相同的半群。 *)

Definition lower_monoid_parent
  : MonoidToSemigroup lower_monoid = lower_semigroup
  := eq_refl.

(** The semigroup stores that exact magma. *)

(** 半群保存完全相同的原群。 *)

Definition lower_semigroup_parent
  : SemigroupToMagma lower_semigroup = lower_magma
  := eq_refl.

(** Actual multiplication is the originally chosen Kan output. *)

(** 实际乘法就是原来选定的 Kan 输出。 *)

Definition lower_product_value (x y : C)
  : @mul _ (hasMagma lower_group) x y = two_sphere_kan_mul X b H x y
  := eq_refl.

(** The unit is the original constant sphere. *)

(** 单位元为原常值球面。 *)

Definition lower_unit_value
  : @mul_unit _ (hasMonoid lower_group) = two_sphere_base X b
  := eq_refl.

(** Inverse is the original actual left-candidate representative. *)

(** 逆为原实际左候选代表。 *)

Definition lower_inverse_value (x : C)
  : @inv _ (hasGroup lower_group) x = (@SphereKanLeftInverse X b K x).1
  := eq_refl.

(** The existing map back to generated classes preserves multiplication. *)

(** 返回生成类的原映射保持乘法。 *)

Definition lower_product_comparison (x y : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@mul _ (hasMagma lower_group) x y) ≈S two_sphere_kan_mul X b H x y.
Proof.
  rewrite lower_product_value.
  exact (two_sphere_cylinder_class_recovery X b KR KC
    (two_sphere_kan_mul X b H x y)).
Defined.

(** The same comparison preserves the constant unit. *)

(** 同一比较保持常值单位。 *)

Definition lower_unit_comparison
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@mul_unit _ (hasMonoid lower_group)) ≈S two_sphere_base X b.
Proof.
  rewrite lower_unit_value.
  exact (two_sphere_cylinder_class_unit X b KR KC).
Defined.

(** The same comparison preserves the selected inverse. *)

(** 同一比较保持选定逆。 *)

Definition lower_inverse_comparison (x : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@inv _ (hasGroup lower_group) x) ≈S
      @inv _ (hasGroup (TwoSphereClassGroup X b H K L)) x.
Proof.
  rewrite lower_inverse_value.
  exact (two_sphere_cylinder_class_recovery X b KR KC
    (@SphereKanLeftInverse X b K x).1).
Defined.

(** Source recovery retains the complete pointwise interface. *)

(** 来源恢复保留完整逐点接口。 *)

Definition lower_source_recovery
  : (two_sphere_class_of_cylinder_resp X b KR KC ∘r
      two_sphere_cylinder_of_class_resp X b KR KC) ≈f id_resp
  := two_sphere_cylinder_class_recovery X b KR KC.

(** Target recovery stores an actual cylinder on the unchanged value. *)

(** 目标恢复保存未改值上的实际柱。 *)

Definition lower_target_recovery (x : C)
  : TwoSphereCylinderHomotopy X b x x
  := two_sphere_class_cylinder_recovery X b KR KC x.

(** Generic inverse Proper consumes actual, rather than generated, equality. *)

(** 通用逆 Proper 消费实际柱相等，而不是生成相等。 *)

Definition lower_inverse_proper (x y : C)
    (E : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereCylinderHomotopy X b
      (@inv _ (hasGroup lower_group) x) (@inv _ (hasGroup lower_group) y)
  := @inv_proper lower_group x y E.

(** Generic involution returns an actual full relative cylinder. *)

(** 通用对合返回实际完整相对柱。 *)

Definition lower_involution (x : C)
  : TwoSphereCylinderHomotopy X b
      (@inv _ (hasGroup lower_group) (@inv _ (hasGroup lower_group) x)) x
  := @inv_inv lower_group x.

(** Generic associativity is available on the same selected parent. *)

(** 通用结合律在相同选定父结构上可用。 *)

Definition lower_associativity (x y z : C)
  : TwoSphereCylinderHomotopy X b
      (@mul _ (hasMagma lower_group) (@mul _ (hasMagma lower_group) x y) z)
      (@mul _ (hasMagma lower_group) x (@mul _ (hasMagma lower_group) y z))
  := @mul_assoc _ (isSemigroup lower_group) x y z.

(** Algebra and full Kan are still not selected by import. *)

(** 导入仍不选择代数或完整 Kan。 *)

Fail Definition lower_no_automatic_group : HasMagma C
  := ltac:(typeclasses eauto).
Fail Definition lower_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X b)
  := ltac:(typeclasses eauto).
Fail Definition lower_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).
Fail Definition lower_missing_candidates : Group
  := TwoSphereCylinderGroup X b KR KC H.

End Lower.

(** ** Higher Native Equality

    Fix the basepoint, two nine-choice families and exactly the old
    three four-horn choices. Native computations below compare only values
    and immediate parents, never structure-law records. *)

(** ** Higher 原生相等

    固定基点、两组九选择及原有三个四维 horn 选择。下列原生计算仅比较值和
    直接父结构，不比较定律记录。 *)

Section Higher.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (KR : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first s)).
Context (KC : ∀ s, HasHornFillers X
  (S (simplex_triangle_horn_face_dim s))
  (simplex_triangle_horn_missing fin_first⁺ s)).
Context `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}.
Context `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}.
Context `{HX4 : !HasHornFillers X 4 fin_first⁺⁺⁺⁺}.
Context (H : HasHornFillers X 3 fin_first⁺⁺)
    (K : HasHornFillers X 3 fin_first⁺⁺⁺)
    (L : HasHornFillers X 3 fin_first⁺).

Let C
  : SetC
  := TwoSphereCylinderS X b KR KC.

(** All four structures retain native-sized representatives. *)

(** 四层结构都保留原生大小的代表。 *)

Definition higher_magma
  : Magma
  := TwoSphereCylinderMagma X b KR KC H.

(** Associativity uses the transported magma. *)

(** 结合律使用运输的原群。 *)

Definition higher_semigroup
  : Semigroup
  := TwoSphereCylinderSemigroup X b KR KC H.

(** Unit laws use the same transported semigroup. *)

(** 单位律使用相同运输半群。 *)

Definition higher_monoid
  : Monoid
  := TwoSphereCylinderMonoid X b KR KC H.

(** Inverse laws use the same transported monoid. *)

(** 逆律使用相同运输幺半群。 *)

Definition higher_group
  : Group
  := TwoSphereCylinderGroup X b KR KC H K L.

(** Each immediate parent is retained by native conversion. *)

(** 每个直接父结构按原生定义转换保留。 *)

Definition higher_group_parent
  : GroupToMonoid higher_group = higher_monoid
  := eq_refl.

(** The monoid stores that exact semigroup. *)

(** 幺半群保存完全相同的半群。 *)

Definition higher_monoid_parent
  : MonoidToSemigroup higher_monoid = higher_semigroup
  := eq_refl.

(** The semigroup stores that exact magma. *)

(** 半群保存完全相同的原群。 *)

Definition higher_semigroup_parent
  : SemigroupToMagma higher_semigroup = higher_magma
  := eq_refl.

(** Actual multiplication is the originally chosen Kan output. *)

(** 实际乘法就是原来选定的 Kan 输出。 *)

Definition higher_product_value (x y : C)
  : @mul _ (hasMagma higher_group) x y = two_sphere_kan_mul X b H x y
  := eq_refl.

(** The unit is the original constant sphere. *)

(** 单位元为原常值球面。 *)

Definition higher_unit_value
  : @mul_unit _ (hasMonoid higher_group) = two_sphere_base X b
  := eq_refl.

(** Inverse is the original actual left-candidate representative. *)

(** 逆为原实际左候选代表。 *)

Definition higher_inverse_value (x : C)
  : @inv _ (hasGroup higher_group) x = (@SphereKanLeftInverse X b K x).1
  := eq_refl.

(** The existing map back to generated classes preserves multiplication. *)

(** 返回生成类的原映射保持乘法。 *)

Definition higher_product_comparison (x y : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@mul _ (hasMagma higher_group) x y) ≈S two_sphere_kan_mul X b H x y.
Proof.
  rewrite higher_product_value.
  exact (two_sphere_cylinder_class_recovery X b KR KC
    (two_sphere_kan_mul X b H x y)).
Defined.

(** The same comparison preserves the constant unit. *)

(** 同一比较保持常值单位。 *)

Definition higher_unit_comparison
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@mul_unit _ (hasMonoid higher_group)) ≈S two_sphere_base X b.
Proof.
  rewrite higher_unit_value.
  exact (two_sphere_cylinder_class_unit X b KR KC).
Defined.

(** The same comparison preserves the selected inverse. *)

(** 同一比较保持选定逆。 *)

Definition higher_inverse_comparison (x : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@inv _ (hasGroup higher_group) x) ≈S
      @inv _ (hasGroup (TwoSphereClassGroup X b H K L)) x.
Proof.
  rewrite higher_inverse_value.
  exact (two_sphere_cylinder_class_recovery X b KR KC
    (@SphereKanLeftInverse X b K x).1).
Defined.

(** Source recovery retains the complete pointwise interface. *)

(** 来源恢复保留完整逐点接口。 *)

Definition higher_source_recovery
  : (two_sphere_class_of_cylinder_resp X b KR KC ∘r
      two_sphere_cylinder_of_class_resp X b KR KC) ≈f id_resp
  := two_sphere_cylinder_class_recovery X b KR KC.

(** Target recovery stores an actual cylinder on the unchanged value. *)

(** 目标恢复保存未改值上的实际柱。 *)

Definition higher_target_recovery (x : C)
  : TwoSphereCylinderHomotopy X b x x
  := two_sphere_class_cylinder_recovery X b KR KC x.

(** Generic inverse Proper consumes actual, rather than generated, equality. *)

(** 通用逆 Proper 消费实际柱相等，而不是生成相等。 *)

Definition higher_inverse_proper (x y : C)
    (E : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereCylinderHomotopy X b
      (@inv _ (hasGroup higher_group) x) (@inv _ (hasGroup higher_group) y)
  := @inv_proper higher_group x y E.

(** Generic involution returns an actual full relative cylinder. *)

(** 通用对合返回实际完整相对柱。 *)

Definition higher_involution (x : C)
  : TwoSphereCylinderHomotopy X b
      (@inv _ (hasGroup higher_group) (@inv _ (hasGroup higher_group) x)) x
  := @inv_inv higher_group x.

(** Generic associativity is available on the same selected parent. *)

(** 通用结合律在相同选定父结构上可用。 *)

Definition higher_associativity (x y z : C)
  : TwoSphereCylinderHomotopy X b
      (@mul _ (hasMagma higher_group) (@mul _ (hasMagma higher_group) x y) z)
      (@mul _ (hasMagma higher_group) x (@mul _ (hasMagma higher_group) y z))
  := @mul_assoc _ (isSemigroup higher_group) x y z.

(** Algebra and full Kan are still not selected by import. *)

(** 导入仍不选择代数或完整 Kan。 *)

Fail Definition higher_no_automatic_group : HasMagma C
  := ltac:(typeclasses eauto).
Fail Definition higher_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy X b)
  := ltac:(typeclasses eauto).
Fail Definition higher_no_full_Kan : HasKanFillers X
  := ltac:(typeclasses eauto).
Fail Definition higher_missing_candidates : Group
  := TwoSphereCylinderGroup X b KR KC H.

End Higher.

Local Transparent TwoSphereCylinderEquivalence TwoSphereClassCylinder
  two_sphere_cylinder_class_iff.
