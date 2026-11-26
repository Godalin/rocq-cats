From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import Algebra.

Set Universe Polymorphism.

Local Open Scope ring_scope.

Fail Minks.Struct OverlappingMonoidExport
  extends Monoid
  exports OverlappingMonoid [Magma, hasMagma].

Fail Minks.Struct SingleBinding
  extends SetC
  with  additive : HasAbGroup.

Example comm_ring_rng_coherence (R : CommRing)
  : RingToRng (CommRingToRing R) = CommRngToRng (CommRingToCommRng R)
  := eq_refl.

Fail Check (λ R : Rng, 1[R]).

(** A shared multiplicative field retains its identity through renaming.
    Its public spelling follows the renamed path in either parent order. *)

Module RenamedKeys.
Minks.Struct ReversedRing
  extends Monoid, Rng.

Example reversed_multiplication (R : ReversedRing)
  : ReversedRing_hasMul R = Monoid_hasMagma (ReversedRingToMonoid R)
    ∧ ReversedRing_hasMul R = Rng_hasMul (ReversedRingToRng R)
  := conj eq_refl eq_refl.

Minks.Struct ProductMagma
  extends Magma
  with  hasMagma as product.
Minks.Inspect hasMul.

Minks.Struct ProductFirst
  extends ProductMagma, Rng.
Minks.Struct MulFirst
  extends Rng, ProductMagma.

Example first_explicit_name (S : ProductFirst) (T : MulFirst)
  : ProductFirst_product S = Rng_hasMul (ProductFirstToRng S)
    ∧ MulFirst_hasMul T = ProductMagma_product (MulFirstToProductMagma T)
  := conj eq_refl eq_refl.

Fail Minks.Struct Reintroduce extends Ring with hasMagma : HasMagma.
Fail Minks.Struct RenameRetired extends Ring with hasMagma as another.
Fail Minks.Struct DependOnRetired
  extends Ring
  with  law : IsComm [carrier, hasEquiv, hasMagma].
Fail Minks.Struct FixRetired extends Ring exports Old [hasMagma].
Fail Minks.Struct LosingName extends MulFirst with product : HasMagma.
Fail Minks.Struct PrematureName
  extends Magma
  with  law : IsComm [carrier, hasEquiv, product], hasMagma as product.

Minks.Struct NamedProduct
  extends Ring
  with  hasMul as product
  exports Relative [Monoid].

Example parent_after_second_rename (S : NamedProduct)
  : NamedProduct_product S = Monoid_hasMagma (NamedProductToMonoid S)
  := eq_refl.

Minks.Struct IndependentOperation
  extends SetC
  with  hasMagma : HasMagma.

Minks.Struct SharedOperation
  extends Rng, IndependentOperation.

Example independent_multiplication (R : SharedOperation)
  : Rng_hasMul (SharedOperationToRng R)
    = IndependentOperation_hasMagma (SharedOperationToIndependentOperation R)
  := eq_refl.

Section LocalRename.
Variable A : Type.
Minks.Struct SelectedPoint
  with  chosen : HasPoint [A], chosen as selected.
End LocalRename.

Minks.Struct NamedPoint (A : Type)
  extends SelectedPoint A
  with  selected as pointChoice.
Fail Minks.Struct ReuseAfterDischarge (A : Type)
  extends NamedPoint A
  with  chosen : HasPoint [A].
Minks.Inspect pointChoice.
End RenamedKeys.

Fail Minks.Struct UnrelatedMonoidExport
  extends Monoid
  exports UnrelatedMonoid [TwoPoints].

(** A cast passes [M] as an explicit value. These instance registrations
    fill class arguments only, so this cast fails. *)

Fail Check (λ M : Monoid, (M : HasMonoid M)).

(** A group interface supplies its inverse component by instance search.
    The monoid interface on the same carrier is a separate export. *)

Section BetweenExports.
Context (A : Type) `{G : !HasGroup A}.

Example selected_inverse
  : (_ : HasInverse A) = HasGroup_hasInverse G
  := eq_refl.

Fail Check (G : HasInverse A).
Fail Check HasGroupToHasMonoid.
Definition implicit_monoid_interface : HasMonoid A := _.
Example same_magma
  : HasMonoid_hasMagma implicit_monoid_interface = HasGroup_hasMagma G
  := eq_refl.
End BetweenExports.

(** The proposed [Minks.Trans IsMonoid to IsMonoidWithPoint] would
    generate the function [fix_unit] written below. Its result fixes
    the point stored in [H] and retains the laws for that point.
    Declaring it as a local coercion enables the first cast. The second
    cast asks for the same laws at an independently chosen [P]. *)

Section ChangingFixedInputs.
Local Coercion fix_unit (M : Magma) (H : IsMonoid M)
  : IsMonoidWithPoint M (IsMonoid_hasPoint H)
  := MakeIsMonoidWithPoint M (IsMonoid_hasPoint H)
       (IsMonoid_isSemigroup H) (IsMonoid_isUnitAt H).

Context (M : Magma) (H : IsMonoid M) (P : HasPoint M).

Check (H : IsMonoidWithPoint M (IsMonoid_hasPoint H)).
Fail Check (H : IsMonoidWithPoint M P).
End ChangingFixedInputs.

(** ** Fixing the magma and its point in two steps

    Both paths start at the same packed monoid. The point extracted over
    its magma indexes the unit laws on the staged path. *)

Section FixCompose.
Context (M : Monoid).

Example fix_compose_point
  : IsMonoid_hasPoint (MonoidToIsMonoid M) = Monoid_hasPoint M
  := eq_refl.

Let staged
  : IsMonoidWithPoint (MonoidToMagma M) (Monoid_hasPoint M)
  := fix_unit (MonoidToMagma M) (MonoidToIsMonoid M).

Let direct := MonoidToIsMonoidWithPoint M.

Example fix_compose_assoc
  : IsMonoidWithPoint_isSemigroup staged = IsMonoidWithPoint_isSemigroup direct
  := eq_refl.

Example fix_compose_unit
  : IsMonoidWithPoint_isUnitAt staged = IsMonoidWithPoint_isUnitAt direct
  := eq_refl.

End FixCompose.

(** The additive and multiplicative monoids of a ring share a carrier.
    Fixing each point must keep the law for that specific operation. *)

Section RingFixedPoints.
Context (R : Ring).

Let additive : Monoid := RngAddGroup R.
Let multiplicative := RingToMonoid R.

Let at_zero
  : IsMonoidWithPoint (MonoidToMagma additive) (Rng_hasZero R)
  := fix_unit (MonoidToMagma additive) (MonoidToIsMonoid additive).

Let at_one
  : IsMonoidWithPoint (MonoidToMagma multiplicative) (Ring_hasOne R)
  := fix_unit (MonoidToMagma multiplicative) (MonoidToIsMonoid multiplicative).

Example additive_unit_is_stored
  : IsMonoidWithPoint_isUnitAt at_zero = Rng_isAddUnit R
  := eq_refl.

Example multiplicative_unit_is_stored
  : IsMonoidWithPoint_isUnitAt at_one = Ring_isUnitAt R
  := eq_refl.

Fail Check (at_zero
  : IsMonoidWithPoint (MonoidToMagma additive) (Ring_hasOne R)).
Fail Check (at_one
  : IsMonoidWithPoint (MonoidToMagma multiplicative) (Rng_hasZero R)).
End RingFixedPoints.

(** Component assembly on a carrier, with a locally enabled canonical packer. *)

Section Completion.
(** On an ordinary type, the field instances of [HasMonoid] supply
    [mul_unit_l]. Building [HasGroup A] also requires an inverse for
    that monoid. With [I], [inv_inv x] uses the inverse mixin directly. *)

Example unit_from_interface (A : Type) `{H : !HasMonoid A} (x : A)
  : point * x ≈ x
  := mul_unit_l x.

Timeout 3 Fail Definition missing_inverse (A : Type) `{H : !HasMonoid A}
  : HasGroup A
  := ltac:(typeclasses eauto).

Definition group_from_interface (A : Type) `{H : !HasMonoid A}
    `{I : !HasInverse A}
  : HasGroup A
  := _.

Example law_from_interface (A : Type) `{H : !HasMonoid A}
    `{I : !HasInverse A} (x : A)
  : inv (inv x) ≈ x
  := inv_inv x.

Definition group_from_packed (M : Monoid) `{I : !HasInverse M}
  : HasGroup M
  := _.

Example law_from_packed (M : Monoid) `{I : !HasInverse M} (x : M)
  : inv (inv x) ≈ x
  := inv_inv x.

(** Enable the reverse canonical only for the positive packing test. With a
    missing component, extraction through this packer can ask for [HasGroup A]
    while that same interface is being assembled. *)

#[local] Canonical group_on_carrier (A : Type) `{H : !HasGroup A}
  : Group
  := GroupOfHasGroup A H.

Definition packed_on_carrier (A : Type) `{H : !HasMonoid A}
    `{I : !HasInverse A}
  : Group
  := A.
End Completion.

(** Completion on a fixed monoid, a second local prototype. At this point
    the registrations from [Completion] have expired. The [IsGroup] export
    generated [MakeIsGroup] and [GroupOfIsGroup]. This section registers
    the latter locally through a canonical packer. *)

Section PackedBaseCompletion.
#[local] Canonical group_on_monoid (M : Monoid) `{R : !IsGroup M}
  : Group
  := GroupOfIsGroup M R.

(** With [R : IsGroup M] in scope, [M] itself can be passed where a
    [Group] is expected. Rocq reverses the coercion to [Monoid]; the local
    canonical [group_on_monoid] supplies the group and instance search
    selects [R]. For [inv_inv x], the exported component projection supplies
    the inverse directly from [R]. *)

Section WithRelativeGroup.
Context (M : Monoid) `{R : !IsGroup M} (x : M).

Example law_from_relative_group
  : inv (inv x) ≈ x
  := inv_inv x.

Definition packed_from_relative_group
  : Group
  := M.
End WithRelativeGroup.

(** The involution law needs only [I]. To reuse the monoid as a packed
    group, the local canonical packer obtains [IsGroup M] from [I]. *)

Section WithInverse.
Context (M : Monoid) `{I : !HasInverse M} (x : M).

Example law_from_inverse
  : inv (inv x) ≈ x
  := inv_inv x.

Definition packed_from_inverse
  : Group
  := M.
End WithInverse.

(** With only [M : Monoid], [group_on_monoid] asks for [IsGroup M].
    Uncomment this section to reproduce the timeout. [relative_from_inverse]
    asks for [HasInverse M], and the exported projection [IsGroup_hasInverse]
    asks for [IsGroup M] again. The depth-four trace shows both steps twice. *)

(*
Section MissingInverse.
#[local] Instance relative_from_inverse (M : Monoid) `{I : !HasInverse M}
  : IsGroup M
  := MakeIsGroup M I.

Context (M : Monoid).

Goal IsGroup M.
Proof.
  Set Typeclasses Debug.
  Fail typeclasses eauto 4.
  Unset Typeclasses Debug.
Abort.

Timeout 2 Definition group_without_inverse : Group := M.
End MissingInverse.
*)
End PackedBaseCompletion.

(** ** Checking the inferred views and witnesses

    These equalities check the selections made in [HierarchyUsage] and
    in the local completion experiments above, after their sections close. *)

Module HierarchyChecks.
Import HierarchyUsage.

Example inferred_parent (G : Group) (x : G)
  : inferred_magma G x = GroupToMagma G
  := eq_refl.

(** The three inferred interfaces reduce to their generated extractions.
    The last check compares the two local searches for [HasMonoid M]. *)

Section MonoidExports.
Context (M : Monoid).

Example fixed_carrier
  : on_carrier M = MonoidToHasMonoid M
  := eq_refl.

Example fixed_magma
  : on_magma M = MonoidToIsMonoid M
  := eq_refl.

Example fixed_point
  : on_point M = MonoidToIsMonoidWithPoint M
  := eq_refl.

Example searched_monoid
  : pass_monoid M = on_carrier M
  := eq_refl.

End MonoidExports.

Example inverse_from_interface {A : Type}
    `{H : !HasMonoid A} `{I : !HasInverse A}
  : HasGroup_hasInverse (@group_from_interface A H I) = I
  := eq_refl.

Example inverse_from_monoid (M : Monoid) `{I : !HasInverse M}
  : HasGroup_hasInverse (@group_from_packed M I) = I
  := eq_refl.

Example inverse_from_relative_group (M : Monoid) `{R : !IsGroup M}
  : Group_hasInverse (@packed_from_relative_group M R) = IsGroup_hasInverse R
  := eq_refl.

Example inverse_from_packed_base (M : Monoid) `{I : !HasInverse M}
  : Group_hasInverse (@packed_from_inverse M I) = I
  := eq_refl.
End HierarchyChecks.

(** ** Export round trips and inherited choices *)

(** The packed-base export retains the selected point of the unital magma. *)

Example packed_monoid_unit (M : Magma) (I : IsMonoid M)
  : (_ : HasPoint M) = IsMonoid_hasPoint I
  := eq_refl.

Example monoid_of_is_monoid (M : Monoid)
  : MonoidOfIsMonoid (MonoidToMagma M) (MonoidToIsMonoid M) = M.
Proof. destruct M. reflexivity. Qed.

Example unit_is_inherited_point (M : UMagma)
  : 1[M] = @point _ (PointedSetC_hasPoint (UMagmaToPointedSetC M))
  := eq_refl.

Example group_export_uses_selected_inverse (M : Monoid) (I : HasInverse M)
  : GroupFromExport_hasInverse (MakeGroupFromExport M (Monoid_hasEquiv M)
      (Monoid_hasMagma M) (Monoid_isSemigroup M) (Monoid_hasPoint M)
      (Monoid_isUnitAt M) I)
    = I
  := eq_refl.

(** Both paths use the same stored carrier, setoid and multiplication. *)

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
    (P : HasPoint S)
    (U : IsUnitAt S (hasPoint := P))
  : MonoidToSemigroup (MonoidOfSemigroup S P U) = S.
Proof. destruct S. reflexivity. Qed.

Example monoid_of_umagma (M : UMagma)
    (A : IsSemigroup M)
  : MonoidToUMagma (MonoidOfUMagma M A) = M.
Proof. destruct M. reflexivity. Qed.

Fail Check MonoidOfMagma.

(** Rocq's coercion through either branch reads this same magma. *)

Example monoid_magma_coercion (M : Monoid)
  : (M : Magma) = MonoidToMagma M
    ∧ ((M : UMagma) : Magma) = MonoidToMagma M
  := conj eq_refl eq_refl.

Definition inferred_assoc_uses_fields (M : Monoid) (x y z : M)
  : inferred_assoc M x y z =
      @mul_assoc M (Monoid_hasEquiv M) (Monoid_hasMagma M)
        (Monoid_isSemigroup M) x y z
  := eq_refl.

Definition inferred_unit_l_uses_field (M : Monoid) (x : M)
  : inferred_unit_l M x =
      @mul_unit_l M (Monoid_hasEquiv M) (Monoid_hasMagma M)
        (Monoid_hasPoint M) (Monoid_isUnitAt M) x
  := eq_refl.

Example unit_with_zero (M : UMagmaWithZero)
  : 1[M] = @point _ (UMagmaWithZero_hasPoint M)
  := eq_refl.

Example ring_multiplication_coherence (R : Ring)
  : RngToSemigroup (RingToRng R) = MonoidToSemigroup (RingToMonoid R)
  := eq_refl.

Example ring_zero_is_additive_unit (R : Ring)
  : 0[R] = 1[RngAddGroup R]
  := eq_refl.

Example ring_one_is_multiplicative_unit (R : Ring)
  : 1[R] = @point _ (Ring_hasOne R)
  := eq_refl.

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
  : @point _
      (PointedSetC_hasPoint (TwoPointsToPointedSetC independent_points))
    = @point _ P
  := eq_refl.

Definition second_point_computes
  : @point _ (TwoPoints_hasOtherPoint independent_points) = @point _ Q
  := eq_refl.

End DistinctPoints.

(** Check that the carrier and equivalence witnesses admit either strict
    ordering. The arity here is specific to the experimental generator. *)

Definition wider_equivalence@{u e | u < e}
    (A : Type@{u}) (E : HasEquiv@{u e} A) (M : @HasMagma@{u e} A E)
  : Magma@{u e}
  := MakeMagma A E M.

Definition wider_carrier@{u e | e < u}
    (A : Type@{u}) (E : HasEquiv@{u e} A) (M : @HasMagma@{u e} A E)
  : Magma@{u e}
  := MakeMagma A E M.
