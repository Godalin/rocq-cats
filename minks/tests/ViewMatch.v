From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksTests Require Import Commands.

(** ** Declare the smaller structure first

    Declaring [Tagged] finds the existing target [PairAt]. *)

Minks.Struct PairAt (p q : HasFlag)
  with  seed : HasFlag,
        chosen : FlagPair [p, q],
        mixed : FlagPair [seed, p].

Minks.Struct Tagged (x y : HasFlag)
  with  seed : HasFlag,
        chosen : FlagPair [x, y],
        mixed : FlagPair [seed, x],
        tag : HasFlag.

Minks.Inspect Tagged.

Check TaggedToPairAt : ∀ x y, Tagged x y → PairAt x y.
Fail Check PairAtToTagged.

Example recovered_pair (x y : HasFlag) (s : Tagged x y)
  : TaggedToPairAt x y s =
      MakePairAt x y (Tagged_seed x y s) (Tagged_chosen x y s) (Tagged_mixed x y s)
  := eq_refl.

(** Parent instantiation permutes the shared descriptors. Discovery must
    recover that permutation when building a view to the independent family. *)

Minks.Struct Reversed (a b : HasFlag)
  extends Tagged b a.

Check ReversedToPairAt : ∀ a b, Reversed a b → PairAt b a.

Example reversed_choice (a b : HasFlag) (s : Reversed a b)
  : PairAt_chosen b a (ReversedToPairAt a b s) = Reversed_chosen a b s
  := eq_refl.

(** An index absent from every descriptor has no determined image.
    The source even offers a unique parameter of the missing type. *)

Minks.Struct Phantom (p q : HasFlag) (z : nat)
  extends PairAt p q.
Minks.Struct Numbered (p q : HasFlag) (n : nat)
  extends Tagged p q.
Check NumberedToPairAt : ∀ p q n, Numbered p q n → PairAt p q.
Fail Check NumberedToPhantom.

(** ** Declare the larger structure first

    Declaring [PairAt] finds the existing source [Tagged]. *)

Module LargerFirst.

Minks.Struct Tagged (x y : HasFlag)
  with  seed : HasFlag,
        chosen : FlagPair [x, y],
        mixed : FlagPair [seed, x],
        tag : HasFlag.

Minks.Struct PairAt (p q : HasFlag)
  with  seed : HasFlag,
        chosen : FlagPair [p, q],
        mixed : FlagPair [seed, p].

Minks.Inspect Tagged.

Check TaggedToPairAt : ∀ x y, Tagged x y → PairAt x y.
Fail Check PairAtToTagged.

Example recovered_pair (x y : HasFlag) (s : Tagged x y)
  : TaggedToPairAt x y s =
      MakePairAt x y (Tagged_seed x y s) (Tagged_chosen x y s) (Tagged_mixed x y s)
  := eq_refl.

End LargerFirst.

(** A packed export uses the same field identities and index substitution
    as the view to its independent base, including through a rename. *)

Minks.Struct TaggedAt (a b : HasFlag)
  extends Tagged b a
  with  chosen as choice
  exports ExtraTag [PairAt].

Check TaggedAtToExtraTag : ∀ a b (s : TaggedAt a b),
  ExtraTag a b (TaggedAtToPairAt a b s).

Example repacked_choice (a b : HasFlag) (base : PairAt b a) (t : ExtraTag a b base)
  : TaggedAt_choice a b (TaggedAtOfExtraTag a b base t) = PairAt_chosen b a base
  := eq_refl.

Example extracted_tag (a b : HasFlag) (s : TaggedAt a b)
  : ExtraTag_tag a b (TaggedAtToExtraTag a b s) = TaggedAt_tag a b s
  := eq_refl.

Fail Minks.Struct TwiceFixed (a b : HasFlag)
  extends TaggedAt a b
  exports Duplicate [PairAt, choice].

Fail Minks.Struct UndeterminedBase (a b : HasFlag)
  extends Tagged a b
  exports MissingIndex [Phantom].

(** Section assumptions and header parameters can determine indices together.
    Only the header parameters are applied before the section closes. *)

Section ScopedIndices.
Context (unused : nat) (x : HasFlag).

Minks.Struct ScopedTagged (y : HasFlag)
  extends Tagged y x
  exports ScopedTag [PairAt].

Check ScopedTaggedToPairAt : ∀ y, ScopedTagged y → PairAt y x.
Check ScopedTaggedToScopedTag : ∀ y (s : ScopedTagged y),
  ScopedTag y (ScopedTaggedToPairAt y s).

Fail Minks.Struct ScopedPhantom (y : HasFlag)
  extends Tagged y x
  exports GuessIndex [Phantom].
End ScopedIndices.

Check ScopedTagged : HasFlag → HasFlag → Type.
Check ScopedTaggedToPairAt : ∀ x y, ScopedTagged x y → PairAt y x.
Example scoped_tag_after_end (x y : HasFlag) (s : ScopedTagged x y)
  : ScopedTag_tag x y (ScopedTaggedToScopedTag x y s) = ScopedTagged_tag x y s
  := eq_refl.

(** A later export failure rolls back the structure and its earlier export.
    The corrected command can reuse all the names. *)

Fail Minks.Struct Retry (a b : HasFlag)
  extends Tagged a b
  exports Extra [PairAt], Empty [Retry].
Fail Check Extra.
Fail Check Retry.
Fail Check RetryToPairAt.
Minks.Struct Retry (a b : HasFlag)
  extends Tagged a b
  exports Extra [PairAt].
Check RetryToExtra : ∀ a b (s : Retry a b), Extra a b (RetryToPairAt a b s).

Module DischargedViews.
Minks.Mixin Select (A : Type) := { pick : A }.
Minks.Struct Big (Y : Type) with point : Select [Y], tag : HasFlag.

(** [X] is fixed inside the section. Once abstracted, the target can take
    the source index, and the new explicit view selects the original field. *)

Section Outer.
Variable unused : nat.
Section Inner.
Variable X : Type.
Minks.Struct Tiny with point : Select [X].
Fail Check BigToTiny.
End Inner.
Check BigToTiny : ∀ X, Big X → Tiny X.
End Outer.
Example selected (X : Type) (b : Big X)
  : Tiny_point X (BigToTiny X b) = Big_point X b
  := eq_refl.
End DischargedViews.

Elpi Query minks.struct lp:{{
  coq.locate "DischargedViews.Big" (indt Big),
  coq.locate "DischargedViews.Tiny" (indt Tiny),
  coq.locate "DischargedViews.BigToTiny" (const View),
  struct-view Big Tiny View explicit-view.
}}.

(** A user declaration later in the section keeps its name when Rocq
    replays library objects during discharge. *)

Module ReservedViewName.
Minks.Mixin Select (A : Type) := { pick : A }.
Minks.Struct Big (Y : Type) with point : Select [Y], tag : HasFlag.
Section S.
Variable X : Type.
Minks.Struct Tiny with point : Select [X].
Definition BigToTiny := true.
End S.
Check BigToTiny : bool.
End ReservedViewName.
