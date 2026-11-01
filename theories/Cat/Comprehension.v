From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Fibration Cat.Pullback.
From Cats Require Import Cat.Arrow.

(** * Comprehension

    A natural projection from total spaces to bases sends cartesian morphisms
    to pullback squares. This property is separate from the choice of lifts. *)

Definition is_comprehension {E B : Cat} {P T : Functor E B} (π : T => P) :=
  ∀ X Y (f : Hom X Y), f ⦂ Cart(P)
    → is_pullback (fmap P f) (π Y) (T X) (π X) (fmap T f).

Record Comprehension {E B : Cat} (P : Functor E B) :=
  { comprehension_lifts : HasCartesianLift P
  ; ExtF : Functor E B
  ; projectionN : ExtF => P
  ; comprehension_universal : is_comprehension projectionN
  }.

Arguments comprehension_lifts {_ _ _} _.
Arguments ExtF {_ _ _} _.
Arguments projectionN {_ _ _} _.
Arguments comprehension_universal {_ _ _} _ {_ _} _ _.

Notation "A '^ext[' K ']'" := (ExtF K A)
  (at level 35, no associativity, format "A ^ext[ K ]") : cat_scope.
Notation "'π[' K ']' A" := (projectionN K A)
  (at level 35, format "π[ K ]  A") : cat_scope.

Theorem comprehension_comm {E B : Cat} {P : Functor E B} (K : Comprehension P)
    {X Y : @Ob E} (f : Hom X Y)
  : π[K] Y ∘ fmap (ExtF K) f ≈ fmap P f ∘ π[K] X.
Proof. apply nt_naturality. Qed.

(** The arrow-category presentation is available for every comprehension.
    Fullness and faithfulness are separate properties, not fields of [K]. *)
Definition ComprehensionF {E B : Cat} {P : Functor E B} (K : Comprehension P)
  : Functor E (Arr B) := NatArrowF (projectionN K).
