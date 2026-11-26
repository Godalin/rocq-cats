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

(** ** Lower Native Equality

    Fix the basepoint, two nine-choice families and exactly the old
    three four-horn choices. Native computations below compare only values
    and immediate parents, never structure-law records. *)

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

Definition lower_magma
  : Magma
  := TwoSphereCylinderMagma X b KR KC H.

(** Associativity uses the transported magma. *)

Definition lower_semigroup
  : Semigroup
  := TwoSphereCylinderSemigroup X b KR KC H.

(** Unit laws use the same transported semigroup. *)

Definition lower_monoid
  : Monoid
  := TwoSphereCylinderMonoid X b KR KC H.

(** Inverse laws use the same transported monoid. *)

Definition lower_group
  : Group
  := TwoSphereCylinderGroup X b KR KC H K L.

(** Each immediate parent is retained by native conversion. *)

Definition lower_group_parent
  : GroupToMonoid lower_group = lower_monoid
  := eq_refl.

(** The monoid stores that exact semigroup. *)

Definition lower_monoid_parent
  : MonoidToSemigroup lower_monoid = lower_semigroup
  := eq_refl.

(** The semigroup stores that exact magma. *)

Definition lower_semigroup_parent
  : SemigroupToMagma lower_semigroup = lower_magma
  := eq_refl.

(** Actual multiplication is the originally chosen Kan output. *)

Definition lower_product_value (x y : C)
  : @mul _ (hasMagma lower_group) x y = two_sphere_kan_mul X b H x y
  := eq_refl.

(** The unit is the original constant sphere. *)

Definition lower_unit_value
  : @mul_unit _ _ (hasUnit lower_group) = two_sphere_base X b
  := eq_refl.

(** Inverse is the original actual left-candidate representative. *)

Definition lower_inverse_value (x : C)
  : @inv _ _ _ (hasInverse lower_group) x = (@SphereKanLeftInverse X b K x).1
  := eq_refl.

(** The existing map back to generated classes preserves multiplication. *)

Definition lower_product_comparison (x y : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@mul _ (hasMagma lower_group) x y) ≈S two_sphere_kan_mul X b H x y.
Proof.
  rewrite lower_product_value.
  exact (two_sphere_cylinder_class_recovery X b KR KC
    (two_sphere_kan_mul X b H x y)).
Defined.

(** The same comparison preserves the constant unit. *)

Definition lower_unit_comparison
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@mul_unit _ _ (hasUnit lower_group)) ≈S two_sphere_base X b.
Proof.
  rewrite lower_unit_value.
  exact (two_sphere_cylinder_class_unit X b KR KC).
Defined.

(** The same comparison preserves the selected inverse. *)

Definition lower_inverse_comparison (x : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@inv _ _ _ (hasInverse lower_group) x) ≈S
      @inv _ _ _ (hasInverse (TwoSphereClassGroup X b H K L)) x.
Proof.
  rewrite lower_inverse_value.
  exact (two_sphere_cylinder_class_recovery X b KR KC
    (@SphereKanLeftInverse X b K x).1).
Defined.

(** Source recovery retains the complete pointwise interface. *)

Definition lower_source_recovery
  : (two_sphere_class_of_cylinder_resp X b KR KC ∘r
      two_sphere_cylinder_of_class_resp X b KR KC) ≈f id_resp
  := two_sphere_cylinder_class_recovery X b KR KC.

(** Target recovery stores an actual cylinder on the unchanged value. *)

Definition lower_target_recovery (x : C)
  : TwoSphereCylinderHomotopy X b x x
  := two_sphere_class_cylinder_recovery X b KR KC x.

(** Generic inverse Proper consumes actual, rather than generated, equality. *)

Definition lower_inverse_proper (x y : C)
    (E : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereCylinderHomotopy X b
      (@inv _ _ _ (hasInverse lower_group) x) (@inv _ _ _ (hasInverse lower_group) y)
  := @inv_proper (GroupToMonoid lower_group) _ (@isInverse _ _ _ (hasInverse lower_group)) x y E.

(** Generic involution returns an actual full relative cylinder. *)

Definition lower_involution (x : C)
  : TwoSphereCylinderHomotopy X b
      (@inv _ _ _ (hasInverse lower_group) (@inv _ _ _ (hasInverse lower_group) x)) x
  := @inv_inv lower_group x.

(** Generic associativity is available on the same selected parent. *)

Definition lower_associativity (x y z : C)
  : TwoSphereCylinderHomotopy X b
      (@mul _ (hasMagma lower_group) (@mul _ (hasMagma lower_group) x y) z)
      (@mul _ (hasMagma lower_group) x (@mul _ (hasMagma lower_group) y z))
  := @mul_assoc _ _ (isSemigroup lower_group) x y z.

(** Algebra and full Kan are still not selected by import. *)

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

Definition higher_magma
  : Magma
  := TwoSphereCylinderMagma X b KR KC H.

(** Associativity uses the transported magma. *)

Definition higher_semigroup
  : Semigroup
  := TwoSphereCylinderSemigroup X b KR KC H.

(** Unit laws use the same transported semigroup. *)

Definition higher_monoid
  : Monoid
  := TwoSphereCylinderMonoid X b KR KC H.

(** Inverse laws use the same transported monoid. *)

Definition higher_group
  : Group
  := TwoSphereCylinderGroup X b KR KC H K L.

(** Each immediate parent is retained by native conversion. *)

Definition higher_group_parent
  : GroupToMonoid higher_group = higher_monoid
  := eq_refl.

(** The monoid stores that exact semigroup. *)

Definition higher_monoid_parent
  : MonoidToSemigroup higher_monoid = higher_semigroup
  := eq_refl.

(** The semigroup stores that exact magma. *)

Definition higher_semigroup_parent
  : SemigroupToMagma higher_semigroup = higher_magma
  := eq_refl.

(** Actual multiplication is the originally chosen Kan output. *)

Definition higher_product_value (x y : C)
  : @mul _ (hasMagma higher_group) x y = two_sphere_kan_mul X b H x y
  := eq_refl.

(** The unit is the original constant sphere. *)

Definition higher_unit_value
  : @mul_unit _ _ (hasUnit higher_group) = two_sphere_base X b
  := eq_refl.

(** Inverse is the original actual left-candidate representative. *)

Definition higher_inverse_value (x : C)
  : @inv _ _ _ (hasInverse higher_group) x = (@SphereKanLeftInverse X b K x).1
  := eq_refl.

(** The existing map back to generated classes preserves multiplication. *)

Definition higher_product_comparison (x y : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@mul _ (hasMagma higher_group) x y) ≈S two_sphere_kan_mul X b H x y.
Proof.
  rewrite higher_product_value.
  exact (two_sphere_cylinder_class_recovery X b KR KC
    (two_sphere_kan_mul X b H x y)).
Defined.

(** The same comparison preserves the constant unit. *)

Definition higher_unit_comparison
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@mul_unit _ _ (hasUnit higher_group)) ≈S two_sphere_base X b.
Proof.
  rewrite higher_unit_value.
  exact (two_sphere_cylinder_class_unit X b KR KC).
Defined.

(** The same comparison preserves the selected inverse. *)

Definition higher_inverse_comparison (x : C)
  : two_sphere_class_of_cylinder_resp X b KR KC
      (@inv _ _ _ (hasInverse higher_group) x) ≈S
      @inv _ _ _ (hasInverse (TwoSphereClassGroup X b H K L)) x.
Proof.
  rewrite higher_inverse_value.
  exact (two_sphere_cylinder_class_recovery X b KR KC
    (@SphereKanLeftInverse X b K x).1).
Defined.

(** Source recovery retains the complete pointwise interface. *)

Definition higher_source_recovery
  : (two_sphere_class_of_cylinder_resp X b KR KC ∘r
      two_sphere_cylinder_of_class_resp X b KR KC) ≈f id_resp
  := two_sphere_cylinder_class_recovery X b KR KC.

(** Target recovery stores an actual cylinder on the unchanged value. *)

Definition higher_target_recovery (x : C)
  : TwoSphereCylinderHomotopy X b x x
  := two_sphere_class_cylinder_recovery X b KR KC x.

(** Generic inverse Proper consumes actual, rather than generated, equality. *)

Definition higher_inverse_proper (x y : C)
    (E : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereCylinderHomotopy X b
      (@inv _ _ _ (hasInverse higher_group) x) (@inv _ _ _ (hasInverse higher_group) y)
  := @inv_proper (GroupToMonoid higher_group) _ (@isInverse _ _ _ (hasInverse higher_group)) x y E.

(** Generic involution returns an actual full relative cylinder. *)

Definition higher_involution (x : C)
  : TwoSphereCylinderHomotopy X b
      (@inv _ _ _ (hasInverse higher_group) (@inv _ _ _ (hasInverse higher_group) x)) x
  := @inv_inv higher_group x.

(** Generic associativity is available on the same selected parent. *)

Definition higher_associativity (x y z : C)
  : TwoSphereCylinderHomotopy X b
      (@mul _ (hasMagma higher_group) (@mul _ (hasMagma higher_group) x y) z)
      (@mul _ (hasMagma higher_group) x (@mul _ (hasMagma higher_group) y z))
  := @mul_assoc _ _ (isSemigroup higher_group) x y z.

(** Algebra and full Kan are still not selected by import. *)

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
