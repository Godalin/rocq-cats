From Cats Require Import Cat.Core.

(** * Sections of a Morphism

    Right-inverse witnesses are retained; equality compares the maps. *)

Definition SectionOfEq {C : Cat} {X Y : @Ob C} (p : Hom X Y)
    (s t : ∃ s : Hom Y X, p ∘ s ≈ id) := s.1 ≈ t.1.

Global Instance SectionOfEq_Equivalence {C : Cat} {X Y : @Ob C} (p : Hom X Y)
  : Equivalence (SectionOfEq p).
Proof.
  split; unfold SectionOfEq.
  - intros s. reflexivity.
  - intros s t H. symmetry. exact H.
  - intros s t u H K. transitivity t.1; assumption.
Defined.

Definition SectionOfS {C : Cat} {X Y : @Ob C} (p : Hom X Y) : SetC :=
  {| carrier := ∃ s : Hom Y X, p ∘ s ≈ id
   ; carrier_equiv := SectionOfEq p
   ; carrier_setoid := SectionOfEq_Equivalence p |}.

Notation "'Sec(' p ')'" := (SectionOfS p) (format "Sec( p )") : cat_scope.
