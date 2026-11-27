From Cats Require Import
  Cat.Monad.Strength.

Local Open Scope monad_scope.

(** Packing over the same endofunctor must keep the selected unit,
    multiplication and strength even with competing instances in scope. *)

Section Choices.
Context {C : Cat} `{MC : !HasMonoidal C} (T : Fct C C)
  (H : HasMonad T) (S : HasStrength T) (K : @IsStrongMonad C MC T H S).
Context `{otherMonad : !HasMonad T} `{otherStrength : !HasStrength T}.

Let M := MakeMonad T H.
Let strong := StrongMonadOfMonad M S K.

Example inferred_unit : η[T]%monad_fct = @monad_unit _ T otherMonad := eq_refl.
Example inferred_mul : μ[T]%monad_fct = @monad_mul _ T otherMonad := eq_refl.
Example selected_unit : η[strong] = @monad_unit _ T H := eq_refl.
Example selected_mul : μ[strong] = @monad_mul _ T H := eq_refl.
Example selected_strength : hasStrength strong = S := eq_refl.
Fail Definition wrong_monad := StrongMonadOfMonad (MakeMonad T otherMonad) S K.
Fail Definition wrong_strength := StrongMonadOfMonad M otherStrength K.

End Choices.
