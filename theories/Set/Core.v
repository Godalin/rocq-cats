From Cats Require Export Meta.

(** * Sets with Specified Equality

    A set is constructively represented by a carrier and a Type-valued
    equivalence relation (a setoid). Rocq's [eq] is one possible choice;
    equality witnesses need not have the same size as carrier elements. *)

Declare Scope set_scope.
Delimit Scope set_scope with set.
Open Scope set_scope.

Record SetC :=
  { carrier :> Type
  ; carrier_equiv : crelation carrier
  ; carrier_setoid :: Equivalence carrier_equiv
  }.

Notation "[≈S]" := (carrier_equiv _).

Infix "≈S" := (carrier_equiv _)
  (at level 50) : set_scope.
