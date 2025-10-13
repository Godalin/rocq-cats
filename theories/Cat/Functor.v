From Cats Require Import Cat.Core.
From Cats Require Import Cat.Set.
Open Scope cat_scope.

Class Functor@{o1 h1 o2 h2}
  (C : Cat@{o1 h1})
  (D : Cat@{o2 h2}) :=
  { F0 : @Ob C → @Ob D
  ; F1 {X Y : @Ob C} : Hom X Y → Hom (F0 X) (F0 Y)

  ; axiom_functor_id {X}
    : F1 (@id X) = @id (F0 X)

  ; axiom_functor_comp {X Y Z} (f : Hom Y Z) (g : Hom X Y)
    : F1 (f ∘ g) = F1 f ∘ F1 g
  }.

Notation "F '.F0'" := (@F0 _ _ F).
Notation "F '.F1'" := (@F1 _ _ F).



(** Identity Functor *)

Program Instance Id {C : Cat} : Functor C C :=
  { F0 X := X
  ; F1 _ _ f := f
  }.



Section Yoneda.
Context `{C : Cat}.
Context {F : Functor (op C) SetC}.

Check SetC.

End Yoneda.
