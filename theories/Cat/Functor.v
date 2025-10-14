From Cats Require Import Cat.Core.
From Cats Require Import Cat.Set.
Open Scope cat_scope.

Record Functor@{o1 h1 o2 h2}
  (C : Cat@{o1 h1})
  (D : Cat@{o2 h2}) :=
  { F0 :> @Ob C → @Ob D
  ; F1 {X Y : @Ob C} : Hom X Y → Hom (F0 X) (F0 Y)

  ; axiom_fmap_proper {X Y}
    :: Proper (@HomEq[X, Y] ==> @HomEq[F0 X, F0 Y]) F1

  ; axiom_functor_id {X}
    : F1 (@id X) ≈ @id (F0 X)

  ; axiom_functor_comp {X Y Z} (f : Hom Y Z) (g : Hom X Y)
    : F1 (f ∘ g) ≈ F1 f ∘ F1 g
  }.

Notation fmap F := (@F1 _ _ F).



(** Identity Functor *)

Program Canonical Structure Id {C : Cat} : Functor C C :=
  {|F0 X := X
  ; F1 _ _ f := f
  |}.
Next Obligation. intros x y. auto. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
