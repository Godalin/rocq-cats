From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  DTT.CwF
  DTT.Context.Extension
  DTT.Context.LiftedRepresentation
  DTT.Context.Elements
  DTT.Context.PairNatural
  DTT.Display.Section
  DTT.Display.Representation.

(** Canonical comparison and both representation squares keep strict native
    Hom orders and two independent target carrier/equality orders. *)

Section CanonicalPairNaturalLevels.
Universes o h p a b c d l v q.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint l < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < v.
Constraint v < q.
Constraint q < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
  (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Let PC := FamBaseF ∘F T.
Let HDC := @ContextElements_HasDisplay C T HC.
Let RC := @DisplayTyTmF C PC HDC.
Let HRC := @Display_HasContextExtension C PC HDC.
Let PD := FamBaseF ∘F U.
Let HDD := @ContextElements_HasDisplay D U HU.
Let RD := @DisplayTyTmF D PD HDD.
Let HRD := @Display_HasContextExtension D PD HDD.

Definition canonical_pair_natural_high_eq_high_target_eq_map
    {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF RC A)
  := @ContextElementsPairN C T HC Γ A.

Definition canonical_pair_natural_high_eq_high_target_eq_iso
    {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ≅N
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF RC A)
  := @context_elements_pair_nat_iso C T HC Γ A.

Definition canonical_pair_natural_high_eq_high_target_eq_inverse
    {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF RC A) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A)
  := @ContextElementsPairInvN C T HC Γ A.

Definition canonical_pair_natural_high_eq_high_target_eq_pair_square
    {Γ : @Ob C} (A : Ty T Γ)
  : (@ContextPairLiftN C RC HRC Γ A ∘Nv @ContextElementsPairN C T HC Γ A
      : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ⇒
          ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)))
      ≈N @ContextPairLiftN C T HC Γ A
  := @context_elements_pair_natural_square C T HC Γ A.

Definition canonical_pair_natural_high_eq_high_target_eq_unpair_square
    {Γ : @Ob C} (A : Ty T Γ)
  : (@ContextElementsPairN C T HC Γ A ∘Nv @ContextUnpairLiftN C T HC Γ A
      : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)) ⇒
          ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF RC A))
      ≈N @ContextUnpairLiftN C RC HRC Γ A
  := @context_elements_unpair_natural_square C T HC Γ A.

Definition canonical_pair_natural_high_eq_low_target_eq_map
    {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF T A) ⇒
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF RC A)
  := @ContextElementsPairN C T HC Γ A.

Definition canonical_pair_natural_high_eq_low_target_eq_iso
    {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF T A) ≅N
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF RC A)
  := @context_elements_pair_nat_iso C T HC Γ A.

Definition canonical_pair_natural_high_eq_low_target_eq_inverse
    {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF RC A) ⇒
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF T A)
  := @ContextElementsPairInvN C T HC Γ A.

Definition canonical_pair_natural_high_eq_low_target_eq_pair_square
    {Γ : @Ob C} (A : Ty T Γ)
  : (@ContextPairLiftN C RC HRC Γ A ∘Nv @ContextElementsPairN C T HC Γ A
      : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF T A) ⇒
          ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)))
      ≈N @ContextPairLiftN C T HC Γ A
  := @context_elements_pair_natural_square C T HC Γ A.

Definition canonical_pair_natural_high_eq_low_target_eq_unpair_square
    {Γ : @Ob C} (A : Ty T Γ)
  : (@ContextElementsPairN C T HC Γ A ∘Nv @ContextUnpairLiftN C T HC Γ A
      : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)) ⇒
          ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF RC A))
      ≈N @ContextUnpairLiftN C RC HRC Γ A
  := @context_elements_unpair_natural_square C T HC Γ A.

Definition canonical_pair_natural_low_eq_high_target_eq_map
    {Γ : @Ob D} (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF U A) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF RD A)
  := @ContextElementsPairN D U HU Γ A.

Definition canonical_pair_natural_low_eq_high_target_eq_iso
    {Γ : @Ob D} (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF U A) ≅N
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF RD A)
  := @context_elements_pair_nat_iso D U HU Γ A.

Definition canonical_pair_natural_low_eq_high_target_eq_inverse
    {Γ : @Ob D} (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF RD A) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF U A)
  := @ContextElementsPairInvN D U HU Γ A.

Definition canonical_pair_natural_low_eq_high_target_eq_pair_square
    {Γ : @Ob D} (A : Ty U Γ)
  : (@ContextPairLiftN D RD HRD Γ A ∘Nv @ContextElementsPairN D U HU Γ A
      : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF U A) ⇒
          ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A)))
      ≈N @ContextPairLiftN D U HU Γ A
  := @context_elements_pair_natural_square D U HU Γ A.

Definition canonical_pair_natural_low_eq_high_target_eq_unpair_square
    {Γ : @Ob D} (A : Ty U Γ)
  : (@ContextElementsPairN D U HU Γ A ∘Nv @ContextUnpairLiftN D U HU Γ A
      : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A)) ⇒
          ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF RD A))
      ≈N @ContextUnpairLiftN D RD HRD Γ A
  := @context_elements_unpair_natural_square D U HU Γ A.

Definition canonical_pair_natural_low_eq_low_target_eq_map
    {Γ : @Ob D} (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF U A) ⇒
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF RD A)
  := @ContextElementsPairN D U HU Γ A.

Definition canonical_pair_natural_low_eq_low_target_eq_iso
    {Γ : @Ob D} (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF U A) ≅N
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF RD A)
  := @context_elements_pair_nat_iso D U HU Γ A.

Definition canonical_pair_natural_low_eq_low_target_eq_inverse
    {Γ : @Ob D} (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF RD A) ⇒
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF U A)
  := @ContextElementsPairInvN D U HU Γ A.

Definition canonical_pair_natural_low_eq_low_target_eq_pair_square
    {Γ : @Ob D} (A : Ty U Γ)
  : (@ContextPairLiftN D RD HRD Γ A ∘Nv @ContextElementsPairN D U HU Γ A
      : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF U A) ⇒
          ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A)))
      ≈N @ContextPairLiftN D U HU Γ A
  := @context_elements_pair_natural_square D U HU Γ A.

Definition canonical_pair_natural_low_eq_low_target_eq_unpair_square
    {Γ : @Ob D} (A : Ty U Γ)
  : (@ContextElementsPairN D U HU Γ A ∘Nv @ContextUnpairLiftN D U HU Γ A
      : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A)) ⇒
          ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF RD A))
      ≈N @ContextUnpairLiftN D RD HRD Γ A
  := @context_elements_unpair_natural_square D U HU Γ A.

Fail Definition canonical_pair_natural_target_too_small {Γ : @Ob C}
    (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{h p _ _ _ _ _}) ∘F ContextPairF T A) ⇒
      ((LiftF : Fct SetCat SetCat@{h p _ _ _ _ _}) ∘F ContextPairF RC A)
  := @ContextElementsPairN C T HC Γ A.
Fail Definition canonical_pair_natural_inverse_target_too_small {Γ : @Ob D}
    (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{p h _ _ _ _ _}) ∘F ContextPairF RD A) ⇒
      ((LiftF : Fct SetCat SetCat@{p h _ _ _ _ _}) ∘F ContextPairF U A)
  := @ContextElementsPairInvN D U HU Γ A.

End CanonicalPairNaturalLevels.
