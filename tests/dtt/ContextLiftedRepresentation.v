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
  DTT.Context.LiftedRepresentation.

(** Lifted representations keep both native Hom orders and two strict
    target carrier/equality orders, with independently large input fibers. *)

Section LiftedContextRepresentationLevels.
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
Fail Definition native_pair_rep_high_eq := @context_extension_nat_iso C T HC.
Fail Definition native_pair_rep_low_eq := @context_extension_nat_iso D U HU.

Definition lifted_context_high_eq_high_target_eq_pair {Γ : @Ob C}
    (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A))
  := @ContextPairLiftN C T HC Γ A.

Definition lifted_context_high_eq_high_target_eq_iso {Γ : @Ob C}
    (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A) ≅N
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A))
  := @context_pair_lifted_nat_iso C T HC Γ A.

Definition lifted_context_high_eq_high_target_eq_unpair {Γ : @Ob C}
    (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF T A)
  := @ContextUnpairLiftN C T HC Γ A.

Definition lifted_context_high_eq_low_target_eq_pair {Γ : @Ob C}
    (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF T A) ⇒
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A))
  := @ContextPairLiftN C T HC Γ A.

Definition lifted_context_high_eq_low_target_eq_iso {Γ : @Ob C}
    (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF T A) ≅N
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A))
  := @context_pair_lifted_nat_iso C T HC Γ A.

Definition lifted_context_high_eq_low_target_eq_unpair {Γ : @Ob C}
    (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A)) ⇒
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF T A)
  := @ContextUnpairLiftN C T HC Γ A.

Definition lifted_context_low_eq_high_target_eq_pair {Γ : @Ob D}
    (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF U A) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A))
  := @ContextPairLiftN D U HU Γ A.

Definition lifted_context_low_eq_high_target_eq_iso {Γ : @Ob D}
    (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF U A) ≅N
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A))
  := @context_pair_lifted_nat_iso D U HU Γ A.

Definition lifted_context_low_eq_high_target_eq_unpair {Γ : @Ob D}
    (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A)) ⇒
      ((LiftF : Fct SetCat SetCat@{v q _ _ _ _ _}) ∘F ContextPairF U A)
  := @ContextUnpairLiftN D U HU Γ A.

Definition lifted_context_low_eq_low_target_eq_pair {Γ : @Ob D}
    (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF U A) ⇒
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A))
  := @ContextPairLiftN D U HU Γ A.

Definition lifted_context_low_eq_low_target_eq_iso {Γ : @Ob D}
    (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF U A) ≅N
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A))
  := @context_pair_lifted_nat_iso D U HU Γ A.

Definition lifted_context_low_eq_low_target_eq_unpair {Γ : @Ob D}
    (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A)) ⇒
      ((LiftF : Fct SetCat SetCat@{q v _ _ _ _ _}) ∘F ContextPairF U A)
  := @ContextUnpairLiftN D U HU Γ A.

Fail Definition lifted_context_target_too_small {Γ : @Ob C} (A : Ty T Γ)
  : ((LiftF : Fct SetCat SetCat@{h p _ _ _ _ _}) ∘F ContextPairF T A) ⇒
      ((LiftF : Fct SetCat SetCat@{h p _ _ _ _ _}) ∘F Hom(-, Γ ▹[T] A))
  := @ContextPairLiftN C T HC Γ A.
Fail Definition lifted_context_reverse_target_too_small {Γ : @Ob D}
    (A : Ty U Γ)
  : ((LiftF : Fct SetCat SetCat@{p h _ _ _ _ _}) ∘F Hom(-, Γ ▹[U] A)) ⇒
      ((LiftF : Fct SetCat SetCat@{p h _ _ _ _ _}) ∘F ContextPairF U A)
  := @ContextUnpairLiftN D U HU Γ A.

End LiftedContextRepresentationLevels.
