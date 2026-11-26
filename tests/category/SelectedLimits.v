From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Pullback.

(** * Registered fixed-category choices

    These test-only bundles exercise both mixins as Minks components.
    Their inherited views must keep the supplied witnesses by conversion. *)

Minks.Struct PullbackChoice
  extends Cat
  with selectedPullback : HasPullback.

Minks.Struct InitialPullbackChoice
  extends PullbackChoice
  with selectedInitial : HasInitial.

Section Choices.
Context (C : Cat) (P Q : HasPullback C) (I J : HasInitial C).

Example inherited_pullback_choice
  : PullbackChoice_selectedPullback
      (InitialPullbackChoiceToPullbackChoice
        (InitialPullbackChoiceOfPullbackChoice (MakePullbackChoice C P) I))
      = P
  := eq_refl.

Example first_initial_choice
  : InitialPullbackChoice_selectedInitial
      (InitialPullbackChoiceOfPullbackChoice (MakePullbackChoice C P) I) = I
  := eq_refl.

Example second_pullback_choice
  : PullbackChoice_selectedPullback (MakePullbackChoice C Q) = Q
  := eq_refl.

Example second_initial_choice
  : InitialPullbackChoice_selectedInitial
      (InitialPullbackChoiceOfPullbackChoice (MakePullbackChoice C Q) J) = J
  := eq_refl.

Example initial_is_same_dual_choice
  : @init C I = @term (C^op) (@hasOpTerminal C I)
  := eq_refl.

(** Rewriting a pullback mediator inside composition uses the category's
    actual Proper instance, after deriving its equality by universality. *)

Lemma mediator_rewriting {X Y Z A B : C}
    (f : Hom X Z) (g : Hom Y Z)
    (a a' : Hom A X) (b b' : Hom A Y)
    (H : f ∘ a ≈ g ∘ b) (H' : f ∘ a' ≈ g ∘ b')
    (Ha : a ≈ a') (Hb : b ≈ b')
    (k : Hom (@Pb C P X Y Z f g) B)
  : k ∘ @pb C P X Y Z f g A a b H
      ≈ k ∘ @pb C P X Y Z f g A a' b' H'.
Proof.
  rewrite (@pb_proper C P X Y Z f g A a b H a' b' H' Ha Hb).
  reflexivity.
Qed.

End Choices.
