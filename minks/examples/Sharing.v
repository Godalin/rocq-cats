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
