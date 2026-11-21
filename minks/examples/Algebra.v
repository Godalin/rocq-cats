From Stdlib Require Import Utf8.
From Minks Require Import all.

Set Universe Polymorphism.

(** * Algebraic mixins and structures

    Mixins name their exact dependencies. Complete records and forgetful
    maps are generated below from the same component graph. *)

(** Choose a Type-valued equivalence on the external carrier. *)

Minks.Mixin HasEquiv@{u e} (A : Type@{u})
  :=
  { equiv : A → A → Type@{e}
  ; equiv_refl : ∀ x, equiv x x
  ; equiv_sym : ∀ x y, equiv x y → equiv y x
  ; equiv_trans : ∀ x y z,
      equiv x y → equiv y z → equiv x z
  }.
Arguments equiv {_ _} _ _.
Infix "≈" := equiv (at level 50).

(** Choose a multiplication respectful for the specified equivalence. *)

Minks.Mixin HasMagma (A : Type)
  extends HasEquiv A
  :=
  { mul : A → A → A
  ; mul_proper : ∀ x x' y y',
      equiv x x' → equiv y y'
        → equiv (mul x y) (mul x' y')
  }.
Arguments mul {_ _ _} _ _.
Infix "*" := mul.

(** Choose a point without requiring an equivalence on its carrier. *)

Minks.Mixin HasPoint (A : Type)
  :=
  { point : A
  }.
Arguments point {_ _}.

(** Require associativity of the selected multiplication. *)

Minks.Mixin IsSemigroup (A : Type)
  extends HasMagma A
  :=
  { mul_assoc : ∀ x y z,
      equiv (mul (mul x y) z) (mul x (mul y z))
  }.

(** Choose a unit for the selected multiplication and witness both unit laws. *)

Minks.Mixin HasUnit (A : Type)
  extends HasMagma A
  :=
  { unit : A
  ; mul_unit_l : ∀ x, equiv (mul unit x) x
  ; mul_unit_r : ∀ x, equiv (mul x unit) x
  }.
Notation "1" := unit.

(** ** Packing mixins into structures

    Build the pointed and multiplicative branches from the same setoid. *)

Minks.Struct SetC
  with  hasEquiv : HasEquiv.

Minks.Struct Magma
  extends SetC
  with  hasMagma : HasMagma.

Minks.Struct PointedSetC
  extends SetC
  with  hasPoint : HasPoint.

Minks.Struct Semigroup
  extends Magma
  with  isSemigroup : IsSemigroup.

Minks.Struct PointedMagma
  extends Magma, PointedSetC.

Minks.Struct UMagma
  extends Magma
  with  hasUnit : HasUnit.

Minks.Struct Monoid
  extends Semigroup, UMagma
  exports HasMonoid,
          IsMonoid [Magma],
          IsMonoidWithUnit [hasUnit, Magma].

Minks.Inspect IsMonoid.
Print IsMonoid.

(** Extend a specified magma with associativity and a unit. *)

Check MonoidToIsMonoid
  : ∀ M : Monoid, IsMonoid (MonoidToMagma M).

Check MonoidOfIsMonoid
  : ∀ M : Magma, IsMonoid M → Monoid.

Definition relative_mul_assoc (M : Magma) `{I : !IsMonoid M} (x y z : M)
  : equiv (mul (mul x y) z) (mul x (mul y z))
  := mul_assoc x y z.

(** The coercion on a packed-base export reads its selected unit. *)

Example packed_monoid_unit (M : Magma) (I : IsMonoid M)
  : (I : HasUnit M) = IsMonoid_hasUnit I
  := eq_refl.

Example monoid_of_is_monoid (M : Monoid)
  : MonoidOfIsMonoid (MonoidToMagma M) (MonoidToIsMonoid M) = M.
Proof. destruct M. reflexivity. Qed.

(** The packed magma comes first because the unit uses its multiplication. *)

Check MonoidOfIsMonoidWithUnit
  : ∀ (M : Magma) (U : @HasUnit M (Magma_hasEquiv M) (Magma_hasMagma M)),
      IsMonoidWithUnit M U → Monoid.

Fail Minks.Struct OverlappingMonoidExport
  extends Monoid
  exports OverlappingMonoid [Magma, hasMagma].

Fail Minks.Struct UnrelatedMonoidExport
  extends Monoid
  exports UnrelatedMonoid [PointedSetC].

(** ** Groups

    Choose a two-sided inverse for the multiplication and unit supplied
    by the exported monoid interface. *)

Minks.Mixin HasInverse (A : Type)
  extends HasMonoid A
  :=
  { inv : A → A
  ; mul_inv_l : ∀ x, equiv (mul (inv x) x) unit
  ; mul_inv_r : ∀ x, equiv (mul x (inv x)) unit
  }.

Minks.Struct Group
  extends Monoid
  with  hasInverse : HasInverse
  exports HasGroup,
          IsGroup [Monoid].

Check GroupOfIsGroup : ∀ M : Monoid, IsGroup M → Group.
Check GroupOfMonoid : ∀ M : Monoid, HasInverse M → Group.

(** Assemble the group interface from an existing monoid and an inverse. *)

Minks.Struct GroupFromExport
  extends Monoid
  with  group : HasGroup.

Example group_export_uses_selected_inverse (M : Monoid) (I : HasInverse M)
  : HasGroup_hasInverse (GroupFromExport_group (GroupFromExportOfMonoid M I))
    = I
  := eq_refl.

(** In any monoid, a left inverse and a right inverse of the same element
    agree in the specified equivalence. *)

Lemma mul_inv_unique (M : Monoid) (x l r : M)
    (Hl : equiv (mul l x) unit) (Hr : equiv (mul x r) unit)
  : equiv l r.
Proof.
  eapply equiv_trans.
  - apply equiv_sym. apply mul_unit_r.
  - eapply equiv_trans.
    + apply mul_proper.
      * apply equiv_refl.
      * apply equiv_sym. exact Hr.
    + eapply equiv_trans.
      * apply equiv_sym. apply mul_assoc.
      * eapply equiv_trans.
        -- apply mul_proper.
           ++ exact Hl.
           ++ apply equiv_refl.
        -- apply mul_unit_l.
Defined.

(** The inherited monoid laws and inverse laws imply involutivity. *)

Lemma inv_inv (G : Group) (x : G)
  : equiv (inv (inv x)) x.
Proof.
  apply (mul_inv_unique G (inv x)).
  - apply mul_inv_l.
  - apply mul_inv_l.
Defined.

(** ** Inherited choices

    Both paths use the same stored carrier, setoid and multiplication. *)

Definition pointed_magma_set_coherence (M : PointedMagma)
  : MagmaToSetC (PointedMagmaToMagma M)
    = PointedSetCToSetC (PointedMagmaToPointedSetC M)
  := eq_refl.

Definition monoid_magma_coherence (M : Monoid)
  : SemigroupToMagma (MonoidToSemigroup M)
    = UMagmaToMagma (MonoidToUMagma M)
  := eq_refl.

(** Pack a monoid from either parent, supplying the component that parent
    lacks. Each forgetful view recovers the supplied parent. *)

Example monoid_of_semigroup (S : Semigroup)
    (U : @HasUnit S (Semigroup_hasEquiv S) (Semigroup_hasMagma S))
  : MonoidToSemigroup (MonoidOfSemigroup S U) = S.
Proof. destruct S. reflexivity. Qed.

Example monoid_of_umagma (M : UMagma)
    (A : @IsSemigroup M (UMagma_hasEquiv M) (UMagma_hasMagma M))
  : MonoidToUMagma (MonoidOfUMagma M A) = M.
Proof. destruct M. reflexivity. Qed.

Fail Check MonoidOfMagma.

(** Rocq's coercion through either branch reads this same magma. *)

Example monoid_magma_coercion (M : Monoid)
  : (M : Magma) = MonoidToMagma M
    ∧ ((M : UMagma) : Magma) = MonoidToMagma M
  := conj eq_refl eq_refl.

(** Use the original class method on the selected multiplication. *)

Definition inferred_assoc (M : Monoid) (x y z : M)
  : equiv (mul (mul x y) z) (mul x (mul y z))
  := mul_assoc x y z.

Definition inferred_assoc_uses_fields (M : Monoid) (x y z : M)
  : inferred_assoc M x y z =
      @mul_assoc M (Monoid_hasEquiv M) (Monoid_hasMagma M)
        (Monoid_isSemigroup M) x y z
  := eq_refl.

(** Use the unit and its law through the same selected mixin. *)

Definition inferred_unit_l (M : Monoid) (x : M)
  : equiv (mul unit x) x
  := mul_unit_l x.

Definition inferred_unit_l_uses_field (M : Monoid) (x : M)
  : inferred_unit_l M x =
      @mul_unit_l M (Monoid_hasEquiv M) (Monoid_hasMagma M)
        (Monoid_hasUnit M) x
  := eq_refl.

(** A matching type does not identify two independently declared slots. *)

Minks.Struct TwoPoints
  extends PointedSetC
  with  hasOtherPoint : HasPoint.

(** Two unlabelled point choices do not provide a default instance. *)

Fail Definition ambiguous_point (P : TwoPoints)
  : HasPoint P
  := ltac:(typeclasses eauto).

(** ** Independent point choices

    On one boolean setoid, choose two point mixins and check which
    choice each projection reads. *)

Section DistinctPoints.
Context (E : HasEquiv bool)
    (P Q : HasPoint bool).

Definition independent_points
  : TwoPoints
  := MakeTwoPoints bool E P Q.

Definition first_point_computes
  : @point bool
      (PointedSetC_hasPoint (TwoPointsToPointedSetC independent_points))
    = @point bool P
  := eq_refl.

Definition second_point_computes
  : @point bool (TwoPoints_hasOtherPoint independent_points) = @point bool Q
  := eq_refl.

End DistinctPoints.

(** Check that the carrier and equivalence witnesses admit either strict
    ordering. The arity here is specific to the experimental generator. *)

Definition wider_equivalence@{u e r | u < e, e < r}
    (A : Type@{u}) (E : HasEquiv@{u e} A) (M : @HasMagma@{u e} A E)
  : Magma@{u r u e}
  := MakeMagma A E M.

Definition wider_carrier@{u e r | e < u, u < r}
    (A : Type@{u}) (E : HasEquiv@{u e} A) (M : @HasMagma@{u e} A E)
  : Magma@{u r u e}
  := MakeMagma A E M.
