From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import
  Algebra
  Commands.

(** * Witness sharing in parent order

    The ordinary parent contributes an unkeyed [HasFlag]. The virtual
    parent contributes two occurrences of the same class with distinct keys. *)

Minks.Struct KeyedFlags
  extends TwoFlags
  exports BothFlags [carrier].

Minks.Mixin PlainFirst (A : Type)
  extends HasFlag, BothFlags A
  :=
  { plain_and_left : @flag hasFlag = @flag (@BothFlags_leftFlag A bothFlags)
  ; plain_and_right : bool * bool :=
      (@flag hasFlag, @flag (@BothFlags_rightFlag A bothFlags))
  }.

Check @PlainFirst : ∀ (left right : HasFlag) (A : Type), Type.

(** The constructor accepts reflexivity for the left flag even when the
    right flag computes to a different boolean. *)

Example plain_shares_only_left (A : Type)
  : @plain_and_right {| flag := true |} {| flag := false |} A
      (@Build_PlainFirst {| flag := true |} {| flag := false |} A eq_refl)
    = (true, false)
  := eq_refl.

Fail Minks.Mixin KeyedFirst (A : Type)
  extends BothFlags A, HasFlag
  := { keyed_first_law : True }.

(** Repeating the same parent contributes one witness. *)

Minks.Mixin RepeatedPoint (A : Type)
  extends HasPoint A, HasPoint A, HasPoint A
  := { repeated_value : A := @point A hasPoint }.

Check @RepeatedPoint : ∀ A : Type, HasPoint A → Type.
Fail Minks.Mixin IncompatiblePoints (A B : Type)
  extends HasPoint A, HasPoint B
  := { unused_points : True }.

(** Two local coercions index the same component in different exports.
    Rocq checks the shared point by conversion when both are inherited. *)

Module ConvertiblePoints.
Record Label := { element : Type }.

Definition values (L : Label)
  := option (element L).
Definition values_alias
  := values.

Minks.Struct Chosen (A : Type)
  with  hasPoint : HasPoint [A].

Minks.Struct FlagOnly
  with  extra : HasFlag.

Module Left.
Local Coercion values : Label >-> Sortclass.
Minks.Struct Choice (L : Label)
  extends Chosen L
  exports LeftPoint [].

Minks.Struct FlaggedChoice (L : Label)
  extends FlagOnly, Chosen L.
End Left.

Module Right.
Local Coercion values_alias : Label >-> Sortclass.
Minks.Struct Choice (L : Label)
  extends Chosen L
  exports RightPoint [].
End Right.

Minks.Mixin SharedPoint (L : Label)
  extends Left.LeftPoint L, Right.RightPoint L, Left.LeftPoint L
  :=
  { left_value : values L := @point _ (Left.LeftPoint_hasPoint L leftPoint)
  ; right_value : values L := @point _ (Right.RightPoint_hasPoint L rightPoint)
  }.

Check @SharedPoint : ∀ L, HasPoint (values L) → Type.

Example shared_value (L : Label) (P : HasPoint (values L))
  : @left_value L P (@Build_SharedPoint L P) =
    @right_value L P (@Build_SharedPoint L P)
  := eq_refl.

Fail Minks.Mixin DifferentLabels (L K : Label)
  extends Left.LeftPoint L, Right.RightPoint K
  := { unused_labels : True }.
(** Both parents contribute the point at convertible indices. It precedes
    the flag from the left parent and is fixed by the bare export. *)

Import Left Right.
Minks.Struct BothChoices (L : Label)
  extends Left.FlaggedChoice L, Right.Choice L
  exports CommonChoice, FixedChoice [hasPoint].

Check @MakeBothChoices : ∀ L, HasPoint (values L) → HasFlag → BothChoices L.
Check @MakeCommonChoice
  : ∀ (L : Label) (P : HasPoint (values L)), HasFlag → CommonChoice L P.
Check @MakeFixedChoice
  : ∀ (L : Label) (P : HasPoint (values L)), HasFlag → FixedChoice L P.
End ConvertiblePoints.

(** * Reuse before filling

    Either flag can fill the first slot in isolation. The type of the
    existing pair determines which choice can reuse both slots. *)

Minks.Struct DiagonalFlag
  extends OneFlag
  exports HasDiagonalFlag [carrier].

Minks.Struct ReuseRight
  extends TwoFlags
  with  diagonal : FlagPair [rightFlag, rightFlag],
        selected : HasDiagonalFlag.

Example reuse_dependent_pair (F : ReuseRight)
  : ReuseRight_selected F =
      MakeHasDiagonalFlag F (ReuseRight_rightFlag F) (ReuseRight_diagonal F)
  := eq_refl.

(** An exact original key has priority even when the alternative flag
    would allow complete reuse. Filling adds a pair on the original flag. *)

Minks.Struct PreferOriginal
  extends Type
  with  hasFlag : HasFlag,
        otherFlag : HasFlag,
        diagonal : FlagPair [otherFlag, otherFlag],
        selected : HasDiagonalFlag.

Example fill_on_original_key (F : PreferOriginal)
  : PreferOriginal_selected F =
      MakeHasDiagonalFlag F (PreferOriginal_hasFlag F) (PreferOriginal_hasPair F)
  := eq_refl.

(** No complete reuse exists without a pair. Filling would have to
    choose between two compatible flags at its very first step. *)

Fail Minks.Struct AmbiguousPartial
  extends TwoFlags
  with  selected : HasDiagonalFlag.

(** * Dependency closure of a fixed selection

    Fixing multiplication also fixes its equivalence and carrier. The
    selected point remains a field and survives extraction and packing. *)

Minks.Struct FixedMultiplication
  extends PointedMagma
  exports PointOnMultiplication [hasMagma],
          PointOnPackedMagma [Magma].

Check @PointOnMultiplication
  : ∀ (A : Type) (E : HasEquiv A) (M : @HasMagma A E), Type.

Example repack_selected_point (A : Type) (E : HasEquiv A)
    (M : @HasMagma A E) (P : HasPoint A)
  : FixedMultiplication_hasPoint
      (FixedMultiplicationOfPointOnMultiplication A E M
        (MakePointOnMultiplication A E M P)) = P
  := eq_refl.

(** Fixing the same multiplication through its packed magma extracts
    definitionally the same remaining point. *)

Example fixed_presentations_agree (F : FixedMultiplication)
  : PointOnPackedMagma_hasPoint (FixedMultiplicationToPointOnPackedMagma F)
    = PointOnMultiplication_hasPoint (FixedMultiplicationToPointOnMultiplication F)
  := eq_refl.

Fail Minks.Struct DuplicateFix
  extends PointedMagma
  exports DuplicatePoint [hasPoint, hasPoint].

(** * Composing relative interfaces over a specified magma

    The operations come from the supplied magma. The point and both
    law witnesses are the components of its relative monoid interface. *)

Minks.Mixin IsIdempotentMonoid (M : Magma)
  extends IsMonoid M
  := { mul_idem : ∀ x : M, x * x ≈ x }.

Check @IsIdempotentMonoid
  : ∀ (M : Magma), IsSemigroup M → ∀ P : HasPoint M,
      IsUnitAt M (hasPoint := P) → Type.

(** Both parents select the same magma. Repeating the monoid interface
    shares its three fields, including the point used by its unit laws. *)

Minks.Mixin IsSingletonMonoid (M : Magma)
  extends IsIdempotentMonoid M, IsMonoid M
  := { all_equiv : ∀ x y : M, x ≈ y }.

Check @IsSingletonMonoid
  : ∀ (M : Magma) (A : IsSemigroup M) (P : HasPoint M)
      (U : IsUnitAt M (hasPoint := P)), @IsIdempotentMonoid M A P U → Type.

Fail Minks.Mixin DifferentMonoids (M N : Magma)
  extends IsIdempotentMonoid M, IsMonoid N
  := { different_monoids : True }.

(** Assemble the two presentations at one magma. The second fixes the
    first one's point and reuses the same associativity and unit laws. *)

Section AtMagma.
Context (M : Magma).

Minks.Struct MonoidOnMagma
  with  laws : IsMonoid [M],
        pointedLaws : IsMonoidWithPoint [M, hasPoint].

Variable N : Magma.
Fail Minks.Struct ConflictingBases
  with  first : IsMonoid [M],
        second : IsMonoid [N].
End AtMagma.

Example assembled_monoid_on_magma (M : Magma)
    (A : IsSemigroup M) (P : HasPoint M) (U : IsUnitAt M (hasPoint := P))
  : let S := MakeMonoidOnMagma M A P U in
    MonoidOnMagma_laws M S = MakeIsMonoid M A P U
    ∧ MonoidOnMagma_pointedLaws M S = MakeIsMonoidWithPoint M P A U
  := conj eq_refl eq_refl.

(** The discharged fields retain their projection paths when the parent
    parameter changes name. A further mixin consumes those exact fields. *)

Section InheritedMagma.
Context (N : Magma).

Minks.Struct IdempotentOnMagma
  extends MonoidOnMagma N
  with  idempotent : IsIdempotentMonoid [N, isSemigroup, hasPoint, isUnitAt].
End InheritedMagma.

Check @IdempotentOnMagmaOfMonoidOnMagma
  : ∀ (N : Magma) (S : MonoidOnMagma N),
      @IsIdempotentMonoid N (MonoidOnMagma_isSemigroup N S)
        (MonoidOnMagma_hasPoint N S) (MonoidOnMagma_isUnitAt N S)
      → IdempotentOnMagma N.
