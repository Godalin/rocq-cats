From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import Algebra.
From MinksTests Require Import Sections.

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
  with  [chosenEquiv, chosenMagma, chosenAssoc, chosenPoint, chosenUnitLaw] : HasMonoid,
        central : HasCentralElement.

Check MonoidByComponents_central.

Fail Minks.Struct MonoidFromSemigroup
  extends Semigroup
  with  : HasMonoid.

(** Reject a shared multiplication with incompatible selected dependencies. *)

Fail Minks.Struct OtherMagma
  extends SetC
  with  hasOtherEquiv : HasEquiv [carrier],
        hasMagma : HasMagma [carrier, hasOtherEquiv].
Fail Check OtherMagma.

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
  : ∀ (A : Type) (x y z : A) (E : HasEquiv A)
      (N : @IsNamedPoint A x E) (P : HasPoint A)
      (L : @IsLeftPoint A x y P E N) (R : @IsRightPoint A x z E N), Type.

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
    (S : @HasSeed A) (I : @IsSeed A x S)
    (y : A) (P : IsSeedAt y)
  : @IsSeedAt A x y S I
  := P.

(** Pass different ordinary parameters to independent parents. *)

Minks.Mixin IndependentChoices (A B : Type)
  extends HasPoint A, HasEquiv B
  :=
  { independent_choice : True }.

Check @IndependentChoices
  : ∀ (A B : Type) (P : HasPoint A) (E : HasEquiv B), Type.

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

(** A qualified key selects its declaration even when another module
    uses the same spelling. Exported witnesses retain these identities. *)

Module FlagA.
Minks.Struct Single with sharedFlag : HasFlag exports SelectedFlag [].
End FlagA.
Module FlagB.
Minks.Struct Single with sharedFlag : HasFlag exports SelectedFlag [].
End FlagB.

Fail Minks.Inspect sharedFlag.
Minks.Inspect FlagA.sharedFlag.
Minks.Inspect FlagB.sharedFlag.

Module ImportedFlags.
Import FlagA.
Minks.Struct Copy with sharedFlag : HasFlag.
Minks.Struct Joined extends Copy, FlagA.Single.
Check @MakeJoined : HasFlag → Joined.
Fail Minks.Struct Wrong (A : Type) with sharedFlag : HasPoint [A].
Import FlagB.
Minks.Inspect sharedFlag.
Fail Minks.Struct Ambiguous with sharedFlag : HasFlag.
Minks.Struct Selected with FlagB.sharedFlag : HasFlag.
End ImportedFlags.

Module LocalFlag.
Minks.Struct First with sharedFlag : HasFlag.
Import FlagA FlagB.
Minks.Struct Second with sharedFlag : HasFlag.
Minks.Struct Joined extends First, Second.
Check @MakeJoined : HasFlag → Joined.
End LocalFlag.

Minks.Struct FlagCopy with FlagA.sharedFlag as copiedFlag : HasFlag.
Check copiedFlag : FlagCopy → HasFlag.
Fail Minks.Struct WrongFlagCopy (A : Type) with FlagA.sharedFlag : HasPoint [A].
Fail Minks.Struct UnknownFlag with FlagA.unknownFlag : HasFlag.

Minks.Mixin BothModuleFlags
  extends FlagA.SelectedFlag, FlagB.SelectedFlag
  := { module_flags : bool * bool :=
         (@flag (FlagA.SelectedFlag_sharedFlag selectedFlag),
          @flag (FlagB.SelectedFlag_sharedFlag selectedFlag0)) }.
Check @BothModuleFlags : HasFlag → HasFlag → Type.

(** A functor application substitutes the class, the component key and
    the export layout together. Qualified access keeps its names scoped. *)

Module Type FlagIndex.
  Parameter item : Set.
End FlagIndex.
Module FlagFamily (X : FlagIndex).
  Minks.Mixin HasItem := { item_value : X.item }.
  Minks.Struct Items with selectedItem : HasItem exports ItemChoice [].
End FlagFamily.
Module BoolIndex <: FlagIndex.
  Definition item := bool.
End BoolIndex.
Module BoolItems := FlagFamily BoolIndex.
Minks.Mixin ReadsItem
  extends BoolItems.ItemChoice
  := { read_item : bool := BoolItems.item_value }.
Minks.Struct CopiedItems with : BoolItems.ItemChoice.
Minks.Inspect BoolItems.selectedItem.
Minks.Inspect BoolItems.Items.
Minks.Struct ExtendedItems
  extends BoolItems.Items.
Check @MakeExtendedItems : BoolItems.HasItem → ExtendedItems.
Minks.Mixin ReadsOrdinaryItem
  extends BoolItems.HasItem
  := { ordinary_item : bool := BoolItems.item_value }.
Check @MakeCopiedItems : BoolItems.HasItem → CopiedItems.
Fail Check item_value.

(** A local key introduces a new choice, even when its class is inherited.
    A projection alias leaves the freshness check on the original key. *)

Module ProjectionNames.
Minks.Struct NamedFlag
  with  chosenFlag as parent_flag : HasFlag.

Minks.Inspect parent_flag.

Fail Minks.Struct RepeatedParent
  extends NamedFlag
  with  chosenFlag : HasFlag.

Fail Minks.Struct RenamedParent
  extends NamedFlag
  with  chosenFlag as child_flag : HasFlag.

Fail Minks.Struct RepeatedLocal
  with  chosenFlag as first_flag : HasFlag,
        chosenFlag as second_flag : HasFlag.

Minks.Struct AnotherFlag
  extends NamedFlag
  with  other as second_flag : HasFlag.

Example other_flag_computes (first second : HasFlag)
  : second_flag (MakeAnotherFlag first second) = second
  := eq_refl.
End ProjectionNames.

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
  with  flagComparison : FlagPair [leftFlag, rightFlag]
  exports HasPairedFlags [carrier].

Check PairedFlags_flagComparison
  : ∀ F : PairedFlags, FlagPair (PairedFlags_leftFlag F) (PairedFlags_rightFlag F).

(** Reordering the two fields preserves their roles. Swapping the
    arguments of the previously registered pair changes its selection. *)

Minks.Struct ReorderedPair
  with  rightFlag : HasFlag,
        leftFlag : HasFlag,
        flagComparison : FlagPair [leftFlag, rightFlag].

Fail Minks.Struct ReversedPair
  with  rightFlag : HasFlag,
        leftFlag : HasFlag,
        flagComparison : FlagPair [rightFlag, leftFlag].

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

Check @HasFlagComparison : ∀ (A : Type) (L R : HasFlag), Type.

Minks.Struct TwoFlagsByExport
  extends Type
  with  as [left_choice, right_choice] : HasTwoFlags.

Example exported_flags_remain_distinct
  : let F := MakeTwoFlagsByExport bool {| flag := true |} {| flag := false |} in
    @flag (left_choice F) = true ∧ @flag (right_choice F) = false
  := conj eq_refl eq_refl.

Minks.Struct OtherTwoFlags
  extends Type
  with  firstFlag : HasFlag,
        secondFlag : HasFlag.

Minks.Struct FourFlags
  extends OtherTwoFlags
  with  : HasTwoFlags.

Fail Minks.Struct DuplicateFlagBinding
  extends OtherTwoFlags
  with  [firstFlag, thirdFlag] : HasTwoFlags.
Fail Minks.Struct ShortFlagBinding
  extends Type
  with  [onlyFlag] : HasTwoFlags.
Fail Minks.Struct ShortFlagAliases
  extends Type
  with  [a, b] as [only_projection] : HasTwoFlags.

(** Omitted fixed inputs see the public keys at the entry. A later
    rename preserves the earlier choice and cannot resolve an ambiguity. *)

Minks.Struct RenameAfterBatch
  extends TwoFlags
  with  [extra] : HasRightFlag, leftFlag as originalLeft.
Fail Minks.Struct PrematurePreference
  extends OtherTwoFlags
  with  [extra] : HasRightFlag, firstFlag as leftFlag.

Minks.Struct RightFlagByExport
  extends OtherTwoFlags
  with  [thirdFlag] as [third_choice] : HasRightFlag [carrier, secondFlag].

Example selected_third_flag (A : Type) (L R T : HasFlag)
  : third_choice (MakeRightFlagByExport A L R T) = T
  := eq_refl.

(** Inspect an imported component key and the declarations that use keys. *)

Minks.Inspect hasMagma.
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
