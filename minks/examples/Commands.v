From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import
  Algebra
  Sections.

(** * Checks for the public commands

    Import a hierarchy from another file, extend one of its records, and
    verify that an incompatible component fails before declaring a record. *)

Minks.Struct ClientMonoid
  extends Algebra.Monoid.
Check ClientMonoidToMonoid : ClientMonoid → Algebra.Monoid.
Check (λ M : ClientMonoid, (M : Algebra.Magma)).

(** The generated ancestor view agrees with projection through the parent. *)

Example client_setoid_view (M : ClientMonoid)
  : ClientMonoidToSetC M = MonoidToSetC (ClientMonoidToMonoid M)
  := eq_refl.

(** The imported record's projection instances are available to clients. *)

Definition imported_assoc (M : Algebra.Monoid) (x y z : M)
  : (x * y) * z ≈ x * (y * z)
  := mul_assoc x y z.

(** Use the exported class as a mixin after importing its declaration.
    Its body can refer to the assembled class, and its type lists the
    equivalence, multiplication, associativity, point and unit laws separately. *)

Minks.Mixin HasCentralElement (A : Type)
  extends HasMonoid A, HasMagma A
  :=
  { central_element : A
  ; central_unit :
      @point _ (HasMonoid_hasPoint hasMonoid) ≈ point
  ; central_comm : ∀ x, central_element * x ≈ x * central_element
  }.

Check @HasCentralElement
  : ∀ (A : Type) (E : HasEquiv A) (M : @HasMagma A E),
      @IsSemigroup A E M → ∀ P : HasPoint A, @IsUnitAt A E M P → Type.

Minks.Struct MonoidByComponents
  extends Type
  with  chosenEquiv : HasEquiv,
        chosenMagma : HasMagma,
        chosenAssoc : IsSemigroup,
        chosenPoint : HasPoint,
        chosenUnitLaw : IsUnitAt,
        hasMonoid : HasMonoid,
        central : HasCentralElement.

Example assembled_monoid_uses_existing_fields (M : MonoidByComponents)
  : MonoidByComponents_hasMonoid M =
      MakeHasMonoid M (MonoidByComponents_chosenEquiv M)
        (MonoidByComponents_chosenMagma M) (MonoidByComponents_chosenAssoc M)
        (MonoidByComponents_chosenPoint M) (MonoidByComponents_chosenUnitLaw M)
  := eq_refl.

Minks.Struct MonoidFromSemigroup
  extends Semigroup
  with  hasMonoid : HasMonoid.

Example assembled_monoid_adds_unit_data (S : Semigroup)
    (P : HasPoint S)
    (U : IsUnitAt S (hasPoint := P))
  : HasMonoid_isUnitAt
      (MonoidFromSemigroup_hasMonoid (MonoidFromSemigroupOfSemigroup S P U)) = U
  := eq_refl.

(** Reject a shared multiplication with incompatible selected dependencies. *)

Minks.Struct OtherMagma
  extends SetC
  with  hasOtherEquiv : HasEquiv [carrier],
        hasMagma : HasMagma [carrier, hasOtherEquiv].
Fail Minks.Struct ConflictingMagma
  extends Magma, OtherMagma.
Fail Check ConflictingMagma.

(** Only Minks declarations supply component metadata. *)

Class OrdinaryChoice (A : Type)
  :=
  { ordinary_choice : A }.

Fail Elpi minks.mixin OrdinaryChoice.
Fail Minks.Struct UnregisteredChoice
  with  hasChoice : OrdinaryChoice.
Fail Minks.Struct ExplicitUnregisteredChoice
  with  hasChoice : OrdinaryChoice [carrier].
Fail Check ExplicitUnregisteredChoice.

Fail Minks.Struct Incomplete
  extends.
Fail Minks.Inspect bool.

(** Extend independent branches on one selected point and one equivalence. *)

Set Universe Polymorphism.

Minks.Mixin IsNamedPoint (A : Type) (x : A)
  extends HasEquiv A
  :=
  { named_point_refl : x ≈ x }.

Minks.Mixin IsLeftPoint (A : Type) (x y : A)
  extends HasPoint A, IsNamedPoint A x
  :=
  { left_point_refl : y ≈ y }.

Minks.Mixin IsRightPoint (A : Type) (x y : A)
  extends IsNamedPoint A x
  :=
  { right_point_refl : y ≈ y }.

Minks.Mixin IsBothPoints (A : Type) (x y z : A)
  extends IsLeftPoint A x y, IsRightPoint A x z
  :=
  { both_points_refl : x ≈ x }.

(** Check the order of the shared and branch-specific parameters. *)

Check @IsBothPoints
  : ∀ (A : Type) (E : HasEquiv A)
      (x : A) (N : @IsNamedPoint A E x) (P : HasPoint A)
      (y : A) (L : @IsLeftPoint A P E x N y)
      (z : A) (R : @IsRightPoint A E x N z), Type.

Fail Minks.Mixin MissingParentArgument (A : Type)
  extends HasEquiv
  :=
  { missing_parent_argument : True }.

Fail Minks.Mixin ConflictingPoints (A : Type) (x y z : A)
  extends IsNamedPoint A x, IsRightPoint A y z
  :=
  { conflicting_points : True }.

(** Keep the braces on the carrier and the index through two extensions. *)

Minks.Mixin HasSeed {A : Type}
  :=
  { seed : A }.

Minks.Mixin IsSeed {A : Type} {x : A}
  extends HasSeed (A := A)
  :=
  { seed_eq : seed = x }.

Minks.Mixin IsSeedAt {A : Type} {x : A} (y : A)
  extends IsSeed (A := A) (x := x)
  :=
  { seed_at : x = y }.

Fail Minks.Mixin MissingImplicitParentArgument {A : Type}
  extends HasSeed
  :=
  { missing_implicit_parent_argument : True }.

Fail Minks.Mixin ExplicitParentApplication {A : Type}
  extends @HasSeed A
  :=
  { explicit_parent_application : True }.

Example inherited_implicit_parameters {A : Type} {x : A}
    (S : @HasSeed A) (I : @IsSeed A S x)
    (y : A) (P : IsSeedAt y)
  : @IsSeedAt A S x I y
  := P.

(** Pass different ordinary parameters to independent parents. *)

Minks.Mixin IndependentChoices (A B : Type)
  extends HasPoint A, HasEquiv B
  :=
  { independent_choice : True }.

Check @IndependentChoices
  : ∀ (A : Type) (P : HasPoint A) (B : Type) (E : HasEquiv B), Type.

(** Sharing dependent arguments keeps their type before them. *)

Minks.Mixin HasIndexedPair (A : Type) (x y : A)
  :=
  { indexed_pair : (A * A)%type := (x, y) }.

Minks.Mixin HasDiagonalPoint (A : Type) (x : A)
  extends HasIndexedPair A x x
  :=
  { diagonal_point : A := x }.

Check @HasDiagonalPoint
  : ∀ (A : Type) (x : A), HasIndexedPair A x x → Type.

(** Use earlier component fields as ordinary arguments. *)

Minks.Mixin HasFlag
  :=
  { flag : bool }.

Minks.Mixin FlagPair (P Q : HasFlag)
  :=
  { flag_pair : bool * bool := (@flag P, @flag Q) }.

Minks.Struct OneFlag
  extends Type
  with  hasFlag : HasFlag,
        hasPair : FlagPair.

Check OneFlag_hasPair
  : ∀ F : OneFlag, FlagPair (OneFlag_hasFlag F) (OneFlag_hasFlag F).

Minks.Struct TwoFlags
  extends Type
  with  leftFlag : HasFlag,
        rightFlag : HasFlag
  exports HasTwoFlags,
          HasRightFlag [carrier, leftFlag].

Definition default_exported_flag (A : Type) (F : HasTwoFlags A)
  : HasFlag
  := ltac:(typeclasses eauto).

Example default_exported_flag_is_left (A : Type) (F : HasTwoFlags A)
  : default_exported_flag A F = HasTwoFlags_leftFlag F
  := eq_refl.

Fail Check (λ (A : Type) (F : HasTwoFlags A), (F : HasFlag)).

Check @HasRightFlag_rightFlag
  : ∀ (A : Type) (L : HasFlag), HasRightFlag A L → HasFlag.

Fail Minks.Struct UnknownExportKey
  extends TwoFlags
  exports HasUnknownKey [missingFlag].

Fail Minks.Struct AmbiguousFlags
  extends TwoFlags
  with  hasPair : FlagPair.

Minks.Struct PairedFlags
  extends TwoFlags
  with  hasPair : FlagPair [leftFlag, rightFlag]
  exports HasPairedFlags [carrier].

Check PairedFlags_hasPair
  : ∀ F : PairedFlags, FlagPair (PairedFlags_leftFlag F) (PairedFlags_rightFlag F).

(** Declaring either endpoint leaves the other export independent. *)

Fail Check HasPairedFlagsToHasRightFlag.

Minks.Struct LeftFlag
  extends Type
  with  leftFlag : HasFlag
  exports HasLeftFlag.

Fail Check HasPairedFlagsToHasLeftFlag.

Minks.Struct SelectedFlag
  extends Type
  with  selectedFlag : HasFlag
  exports HasSelectedFlag.

Fail Check HasPairedFlagsToHasSelectedFlag.

(** Keep distinct fields of the same class throughout expansion. *)

Minks.Mixin HasFlagComparison (A : Type)
  extends HasTwoFlags A
  :=
  { flags_agree :
      @flag (@HasTwoFlags_leftFlag A hasTwoFlags) =
      @flag (@HasTwoFlags_rightFlag A hasTwoFlags)
  }.

Check @HasFlagComparison : ∀ (L R : HasFlag) (A : Type), Type.

Minks.Struct TwoFlagsByExport
  extends Type
  with  flags : HasTwoFlags.

Example assembled_flags_remain_distinct
  : @flag (HasTwoFlags_leftFlag
      (TwoFlagsByExport_flags (MakeTwoFlagsByExport bool {| flag := true |}
        {| flag := false |}))) = true
    ∧ @flag (HasTwoFlags_rightFlag
      (TwoFlagsByExport_flags (MakeTwoFlagsByExport bool {| flag := true |}
        {| flag := false |}))) = false
  := conj eq_refl eq_refl.

Minks.Struct OtherTwoFlags
  extends Type
  with  firstFlag : HasFlag,
        secondFlag : HasFlag.

Fail Minks.Struct AmbiguousFlagAssembly
  extends OtherTwoFlags
  with  flags : HasTwoFlags.

Minks.Struct RightFlagByExport
  extends OtherTwoFlags
  with  flags : HasRightFlag [carrier, secondFlag].

Example assembled_flags_respect_explicit_selection (F : RightFlagByExport)
  : @HasRightFlag_rightFlag F (RightFlagByExport_secondFlag F)
      (RightFlagByExport_flags F) = RightFlagByExport_firstFlag F
  := eq_refl.

Minks.Inspect HasRightFlag.
Minks.Inspect RightFlagByExport.

(** Discover a proper structural view once both records exist. *)

Minks.Struct EarlierPointed
  extends Type
  with  chosenPoint : HasPoint,
        chosenEquiv : HasEquiv.

Minks.Struct LaterPoint
  extends Type
  with  chosenPoint : HasPoint.

Example earlier_view_preserves_point (S : EarlierPointed)
  : LaterPoint_chosenPoint (EarlierPointedToLaterPoint S)
    = EarlierPointed_chosenPoint S
  := eq_refl.

Minks.Struct LaterPointed
  extends Type
  with  chosenPoint : HasPoint,
        secondEquiv : HasEquiv
  exports EquivOnLaterPoint [LaterPoint].

(** A structurally matched base has an explicit extraction. *)

Check LaterPointedToEquivOnLaterPoint
  : ∀ S : LaterPointed, EquivOnLaterPoint (LaterPointedToLaterPoint S).

Fail Definition inferred_on_structural_base (S : LaterPointed)
  : EquivOnLaterPoint (LaterPointedToLaterPoint S)
  := _.

Example later_view_preserves_point (S : LaterPointed)
  : LaterPoint_chosenPoint (LaterPointedToLaterPoint S)
    = LaterPointed_chosenPoint S
  := eq_refl.

Fail Check (λ S : EarlierPointed, (S : LaterPoint)).
Fail Check LaterPointToEarlierPointed.

(** The imported mixin still exposes the implicit carrier generalized by Rocq. *)

Minks.Mixin ImportedChoice (B : Type) (x : B)
  extends Sections.HasAgain (A := B) x
  := { imported_choice : B }.

Section ImportedFamily.
Context (D : Type).
Minks.Struct ImportedLabel
  extends Sections.FurtherLabel D.
End ImportedFamily.

Example imported_label_view (D : Type) (P : ImportedLabel D)
  : ImportedLabelToLabelledPoint D P =
      FurtherLabelToLabelledPoint D (ImportedLabelToFurtherLabel D P)
  := eq_refl.
