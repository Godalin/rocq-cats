From Cats Require Import
  Cat.Computational.Arrow.Static.

(** Separate choices assemble on the original category. The static Arrow
    consumes exactly the products selected by its Applicative. *)

Section Components.
Context {C : Cat} `{T : !HasTerminal C} `{P : !HasProduct C}
  `{E : !HasExponential P}.

Example assemble_cartesian : HasCartesian C := _.
Example assemble_closed : HasCC C := _.

Example selected_components : assemble_closed = MakeHasCC C T P E := eq_refl.

Context (A : Applicative C).
Example static_from_components : Arrow C (StaticCat (C := C) A)
  := StaticArrow (C := C) A.

End Components.

(** A cartesian choice extends to a closed choice given exponentials for
    its own product. *)

Section ExtendCartesian.
Context {C : Cat} `{HC : !HasCartesian C}.

Fail Definition missing_exponentials : HasCC C := _.

Context `{E : !HasExponential (HasCartesian_hasProduct HC)}.

Example extend_cartesian : HasCC C := _.
Example extended_product
  : HasCC_hasProduct extend_cartesian = HasCartesian_hasProduct HC
  := eq_refl.
Example extended_exponential
  : HasCC_hasExponential extend_cartesian = E := eq_refl.

End ExtendCartesian.

(** Restriction uses the selected product. Exponentials for a different
    product cannot extend that same selection. *)

Section RestrictClosed.
Context {C : Cat} `{CC : !HasCC C}.

Example restrict_closed : HasCartesian C := _.
Example restricted_product
  : HasCartesian_hasProduct restrict_closed = HasCC_hasProduct CC
  := eq_refl.

Context (other : HasProduct C) (E : HasExponential other).

Fail Definition mismatched_product :=
  MakeHasCC C (HasCC_hasTerminal CC) (HasCC_hasProduct CC) E.

End RestrictClosed.

(** Bundled categories supply the same choices through instance search. *)

Definition packed_cartesian (C : CartCat) : HasCartesian C := _.
Example packed_product (C : CartCat)
  : HasCartesian_hasProduct (packed_cartesian C) = hasProduct C := eq_refl.

Definition packed_closed (C : CCC) : HasCC C := _.
Example packed_exponential (C : CCC)
  : HasCC_hasExponential (packed_closed C) = hasExponential C := eq_refl.
