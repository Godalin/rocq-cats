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
      x ≈ x' → y ≈ y'
        → mul x y ≈ mul x' y'
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
      (x * y) * z ≈ x * (y * z)
  }.

(** Require the inherited point to be a two-sided unit for this multiplication. *)

Minks.Mixin IsUnitAt (A : Type)
  extends HasMagma A, HasPoint A
  :=
  { mul_unit_l : ∀ x,
      point * x ≈ x
  ; mul_unit_r : ∀ x,
      x * point ≈ x
  }.

(** ** Packing mixins into structures

    Build the pointed and multiplicative branches from the same setoid. *)

Minks.Struct SetC
  extends Type
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
  extends PointedMagma
  with  isUnitAt : IsUnitAt.

Notation "1[ M ]" := (@point _ (UMagma_hasPoint M))
  (at level 0).

Minks.Struct Monoid
  extends Semigroup, UMagma
  exports HasMonoid [carrier],
          IsMonoid [Magma],
          IsMonoidWithPoint [hasPoint, Magma].

(** Extend a specified magma with associativity and a unit. *)

Check MonoidToIsMonoid
  : ∀ M : Monoid, IsMonoid (MonoidToMagma M).

Check MonoidOfIsMonoid
  : ∀ M : Magma, IsMonoid M → Monoid.

Definition relative_mul_assoc (M : Magma)
    `{I : !IsMonoid M} (x y z : M)
  : (x * y) * z ≈ x * (y * z)
  := mul_assoc x y z.

(** Fix the packed magma and its chosen point; the unit laws remain fields. *)

Check MonoidOfIsMonoidWithPoint
  : ∀ (M : Magma) (P : HasPoint M), IsMonoidWithPoint M P → Monoid.

(** ** Groups

    Choose a two-sided inverse for the multiplication and unit supplied
    by the exported monoid interface. *)

Minks.Mixin HasInverse (A : Type)
  extends HasMonoid A
  :=
  { inv : A → A
  ; mul_inv_l : ∀ x,
      inv x * x ≈ point
  ; mul_inv_r : ∀ x,
      x * inv x ≈ point
  }.

(** In any monoid, a left inverse and a right inverse of the same element
    agree in the specified equivalence. *)

Lemma mul_inv_unique {A : Type} `{S : IsSemigroup A}
    `{P : !HasPoint A} `{U : !IsUnitAt A} (x l r : A)
    (Hl : l * x ≈ point) (Hr : x * r ≈ point)
  : l ≈ r.
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

Lemma inv_inv {A : Type} `{I : HasInverse A} (x : A)
  : inv (inv x) ≈ x.
Proof.
  apply (mul_inv_unique (inv x)).
  - apply mul_inv_l.
  - apply mul_inv_l.
Defined.

Minks.Struct Group
  extends Monoid
  with  hasInverse : HasInverse
  exports HasGroup [carrier],
          IsGroup [Monoid].

Check GroupOfIsGroup.
Check GroupOfMonoid.

(** Expand the carrier-relative group interface in constructor order. *)

Minks.Struct GroupFromExport
  extends Type
  with  : HasGroup.

(** ** Rings on one setoid

    The inherited semigroup operation is multiplication. Addition uses a
    second respectful operation on the same setoid, with its own unit. *)

(** Commutativity requires only a respectful binary operation. *)

Minks.Mixin IsComm (A : Type)
  extends HasMagma A
  :=
  { mul_comm : ∀ x y, x * y ≈ y * x }.

Minks.Struct CommMagma
  extends Magma
  with isComm : IsComm.

Minks.Struct AbGroup
  extends CommMagma, Group
  exports HasAbGroup [hasEquiv],
          IsAbGroupAt [hasMagma, hasPoint].

Minks.Inspect AbGroup.

(** Over a setoid, all additive operations and laws come from the export. *)

Module AbelianGroupAssembly.
Minks.Struct Packed
  extends SetC
  with  : HasAbGroup.
Minks.Inspect HasAbGroup.

Check Packed_hasInverse.
End AbelianGroupAssembly.

Declare Scope ring_scope.

(** Both distributivity laws refer to the same two selected operations. *)

Section Distributivity.
Context (A : Type) (E : HasEquiv A) (addOp mulOp : @HasMagma A E).

Local Infix "+" := (@mul _ _ addOp)
  (at level 50, left associativity)
  : ring_scope.
Local Infix "*" := (@mul _ _ mulOp)
  (at level 40, left associativity)
  : ring_scope.
Local Open Scope ring_scope.

Minks.Mixin IsDistributive
  :=
  { mul_add_l : ∀ x y z, (x * (y + z)) ≈ (x * y + x * z)
  ; mul_add_r : ∀ x y z, (x + y) * z ≈ (x * z + y * z)
  }.

End Distributivity.

Minks.Inspect IsDistributive.

(** A rng has an additive abelian group and associative multiplication.
    The assembled additive view uses the selected addition and zero. *)

Minks.Struct Rng
  extends Semigroup
  with  hasMagma as hasMul,
        [hasAdd, isAddComm, isAddAssoc, hasZero,
          isAddUnit, hasNeg] : HasAbGroup,
        isDistrib : IsDistributive [carrier, hasEquiv, hasAdd, hasMul].

Definition RngAddGroup (R : Rng)
  : AbGroup
  := MakeAbGroup R (Rng_hasEquiv R) (Rng_hasAdd R) (Rng_isAddComm R)
       (Rng_isAddAssoc R) (Rng_hasZero R) (Rng_isAddUnit R) (Rng_hasNeg R).

(** Joining the multiplicative monoid adds its selected one and unit laws.
    A commutative ring also makes this multiplication commutative. *)

Minks.Struct Ring
  extends Rng, Monoid
  with  hasPoint as hasOne
  exports IsRingOps [hasMul, hasAdd].

(** Multiplicative commutativity already makes sense without a one. *)

Minks.Struct CommRng
  extends Rng, CommMagma
  with  isComm as isMulComm.

Minks.Struct CommRing
  extends Ring, CommRng.

(** The index selects both the setoid and the operation. *)

Notation "x +[ R ] y" := (@mul _ _ (Rng_hasAdd R) x y)
  (at level 50, left associativity)
  : ring_scope.
Notation "x *[ R ] y" := (@mul _ _ (Magma_hasMagma R) x y)
  (at level 40, left associativity)
  : ring_scope.
Notation "0[ R ]" := (@point _ (Rng_hasZero R))
  (at level 0)
  : ring_scope.
Local Open Scope ring_scope.

(** ** Fields

    A field has distinct zero and one and a chosen reciprocal for each
    element [x] equipped with a proof that [x ≈ 0] implies [False]. *)

Minks.Mixin HasFieldInverse (A : Type) (Z O : HasPoint A)
  extends HasMagma A
  :=
  { zero_ne_one : (@point A Z ≈ @point A O) → False
  ; recip : ∀ x : A, (x ≈ @point A Z → False) → A
  ; mul_recip_r : ∀ x nz, x * recip x nz ≈ @point A O
  }.

(** Commutativity gives the other inverse law. Uniqueness then compares
    reciprocals at equivalent inputs with independently supplied proofs. *)

Section ReciprocalLaws.
Context {A : Type} {E : HasEquiv A} {M : @HasMagma A E}
  {Z O : HasPoint A} {H : @HasFieldInverse A Z O E M}
  {C : @IsComm A E M}.

Lemma mul_recip_l (x : A) (nz : x ≈ @point A Z → False)
  : recip x nz * x ≈ @point A O.
Proof.
  eapply equiv_trans. apply mul_comm. apply mul_recip_r.
Qed.

Context {S : @IsSemigroup A E M} {U : @IsUnitAt A E M O}.

Lemma recip_proper (x y : A) (nx : x ≈ @point A Z → False)
    (ny : y ≈ @point A Z → False) (h : x ≈ y)
  : recip x nx ≈ recip y ny.
Proof.
  apply (@mul_inv_unique A E M S O U x).
  - apply mul_recip_l.
  - eapply equiv_trans.
    + apply mul_proper. exact h. apply equiv_refl.
    + apply mul_recip_r.
Qed.
End ReciprocalLaws.

Minks.Struct Field
  extends CommRing
  with  hasFieldInverse
          : HasFieldInverse
            [carrier, hasZero, hasOne, hasEquiv, hasMul].

Check RngToSemigroup : Rng → Semigroup.
(** *** The field with two elements

    Exclusive or is addition, conjunction is multiplication, and every
    element is its own additive inverse. All operations compute on booleans. *)

Module ModTwo.

Definition BoolEquiv
  : HasEquiv bool
  :=
  {| equiv := @eq bool
  ; equiv_refl := @eq_refl bool
  ; equiv_sym := @eq_sym bool
  ; equiv_trans := @eq_trans bool
  |}.

Definition BoolOp (f : bool → bool → bool)
  : @HasMagma bool BoolEquiv.
Proof.
  refine {| mul := f |}.
  intros x x' y y' -> ->. reflexivity.
Defined.

Local Abbreviation add := (BoolOp xorb).
Local Abbreviation times := (BoolOp andb).
Local Abbreviation zero := ({| point := false |} : HasPoint bool).
Local Abbreviation one := ({| point := true |} : HasPoint bool).

Lemma add_assoc
  : @IsSemigroup _ _ add.
Proof. constructor. intros [] [] []; reflexivity. Qed.

Lemma times_assoc
  : @IsSemigroup _ _ times.
Proof. constructor. intros [] [] []; reflexivity. Qed.

Lemma add_unit
  : @IsUnitAt _ _ add zero.
Proof. constructor; intros []; reflexivity. Qed.

Lemma times_unit
  : @IsUnitAt _ _ times one.
Proof. constructor; intros []; reflexivity. Qed.

Definition Neg
  : @HasInverse _ _ add add_assoc zero add_unit.
Proof. refine {| inv := λ x, x |}; intros []; reflexivity. Defined.

Lemma add_comm
  : @IsComm _ _ add.
Proof. constructor. intros [] []; reflexivity. Qed.

Lemma times_comm
  : @IsComm _ _ times.
Proof. constructor. intros [] []; reflexivity. Qed.

Lemma distrib
  : IsDistributive bool BoolEquiv add times.
Proof. constructor; intros [] [] []; reflexivity. Qed.

Definition F2Ring
  : CommRing
  := CommRingOfRing
       (RingOfRng
         (MakeRng bool BoolEquiv times times_assoc add add_comm
           add_assoc zero add_unit Neg distrib)
         one times_unit)
       times_comm.

Definition F2Inverse
  : @HasFieldInverse bool zero one BoolEquiv times.
Proof.
  refine {| recip := λ x _, x |}.
  - discriminate.
  - intros [] nz. reflexivity. destruct (nz eq_refl).
Defined.

Definition F2
  : Field
  := FieldOfCommRing F2Ring F2Inverse.

Definition selected_ring_point (R : Ring)
  : R
  := point.

Example default_ring_point (R : Ring)
  : selected_ring_point R = 0[R]
  := eq_refl.

Example distinct_constants
  : 0[F2] ≠ 1[F2].
Proof. discriminate. Qed.

Example reciprocal_of_one (nz : 1[F2] ≈ 0[F2] → False)
  : recip 1[F2] nz = 1[F2]
  := eq_refl.

Example one_plus_one
  : 1[F2] +[F2] 1[F2] = 0[F2]
  := eq_refl.

Example one_times_one
  : 1[F2] *[F2] 1[F2] = 1[F2]
  := eq_refl.

End ModTwo.

(** Use the original class method on the selected multiplication. *)

Definition inferred_assoc (M : Monoid) (x y z : M)
  : (x * y) * z ≈ x * (y * z)
  := mul_assoc x y z.

(** Use the unit and its law through the same selected mixin. *)

Definition inferred_unit_l (M : Monoid) (x : M)
  : 1[M] * x ≈ x
  := mul_unit_l x.

(** A matching type does not identify two independently declared slots. *)

Minks.Struct TwoPoints
  extends PointedSetC
  with  hasOtherPoint : HasPoint.

(** A second point does not change the point used by the unit laws. *)

Minks.Struct UMagmaWithZero
  extends UMagma
  with  hasZero : HasPoint.

Example selected_unit_with_zero_l (M : UMagmaWithZero) (x : M)
  : 1[M] * x ≈ x
  := mul_unit_l x.

(** ** Using the algebra hierarchy

    - [Packed] and [PointSelection] use registrations made by [Minks.Struct].
    - [ExportInstances] and [PackedToExport] use the extraction instances
      generated by the three exports of [Monoid]. *)

Module HierarchyUsage.

(** Parent coercions. Declaring [Group] registers its direct edge to [Monoid].
    The cast to [Magma] follows the registered parent edges. *)

Section Packed.
Context (G : Group) (x : G).

Check (G : Monoid).
Check (G : Magma).
(** Component instances. Declaring [Group] also registers its unique
    mixin projections. They supply the inputs to [inv], [mul_inv_l],
    multiplication, the selected point and its equivalence. *)

Check (inv x : G).
Check mul_inv_l x : inv x * x ≈ point.

(** Canonical inference. The type of [x] fixes the carrier of the
    implicit magma in [magma_of_element x]. The ancestor view
    [GroupToMagma] was registered as canonical when [Group] was declared. *)

Definition magma_of_element {M : Magma} (_ : M)
  : Magma
  := M.

Definition inferred_magma
  : Magma
  := magma_of_element x.

End Packed.

(** Each export registers its extraction. The index selects the carrier,
    the magma, or the magma and point of the supplied monoid. *)

Section ExportInstances.
Context (M : Monoid).

Definition on_carrier
  : HasMonoid M
  := _.

Definition on_magma
  : IsMonoid (MonoidToMagma M)
  := _.

Definition on_point
  : IsMonoidWithPoint (MonoidToMagma M) (Monoid_hasPoint M)
  := _.

End ExportInstances.

(** Extraction remains available after the preceding section closes. *)

Section PackedToExport.
Definition pass_monoid (M : Monoid)
  : HasMonoid M
  := _.
End PackedToExport.

(** The inherited first point is the default. Both keys have projections. *)

Section PointSelection.
Context (S : TwoPoints).

Definition selected_point
  : HasPoint S
  := _.

Example default_point
  : selected_point = TwoPoints_hasPoint S
  := eq_refl.
Check @point S (TwoPoints_hasPoint S).
Check @point S (TwoPoints_hasOtherPoint S).
End PointSelection.

End HierarchyUsage.
