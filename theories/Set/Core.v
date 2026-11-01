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

(** Explicit wrappers raise carrier and equality-witness levels separately.
    Both lower maps compute by projection; no resizing is assumed. *)
Record LiftT@{u v} (A : Type@{u}) : Type@{v} := { lower : A }.
Arguments lower {_} _.

Program Definition LiftS@{u p v q +} (X : SetC@{u p}) : SetC@{v q} :=
  {| carrier := LiftT@{u v} X
   ; carrier_equiv x y := LiftT@{p q} (lower x ≈S lower y) |}.
Next Obligation.
  split.
  - intros [x]. exact {| lower := reflexivity x |}.
  - intros [x] [y] [H]. exact {| lower := symmetry H |}.
  - intros [x] [y] [z] [H] [K]. exact {| lower := transitivity H K |}.
Defined.

Notation "'↑S' X" := (LiftS X) (at level 35) : set_scope.
