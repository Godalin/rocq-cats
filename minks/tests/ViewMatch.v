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
