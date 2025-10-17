From Cats Require Import Cat.Core.
From Cats Require Import Cat.Set.
Open Scope cat_scope.



(** * Functor *)

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



(** ** Identity Functor *)

Program Canonical Structure IdF {C : Cat} : Functor C C :=
  {|F0 X := X
  ; F1 _ _ f := f
  |}.
Next Obligation. intros x y. auto. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Program Canonical Structure CompF {C D E : Cat}
    (G : Functor D E) (F : Functor C D) :=
  {|F0 X := (G (F X))
  ; F1 _ _ f := fmap G (fmap F f)
  |}.
Next Obligation. intros f g H.
  rewrite axiom_fmap_proper. reflexivity.
  rewrite axiom_fmap_proper. reflexivity. auto.
Qed.
Next Obligation.
  repeat rewrite axiom_functor_id. reflexivity.
Qed.
Next Obligation.
  repeat rewrite axiom_functor_comp. reflexivity.
Qed.

(** Equality between Functors. *)

Definition FunctorEq {C D : Cat} (F G : Functor C D)
  := ∀ X, F X = G X.

Instance FunctorEq_Equivalence {C D}
  : Equivalence (@FunctorEq C D).
Proof. split.
  - intros F X. reflexivity.
  - intros F G H X. symmetry. auto.
  - intros F G H H1 H2 X. transitivity (G X); auto.
Qed.

Infix "∘F" := CompF
  (at level 40) : cat_scope.

Infix "=F" := FunctorEq
  (at level 50) : cat_scope.



(** ** Category of small categories *)

Program Instance CatCat : Cat :=
  { Ob := Cat
  ; Hom C D := Functor C D
  ; HomEq _ _ := FunctorEq
  ; id _ := IdF
  ; comp _ _ _ := CompF
  }.
Next Obligation. split. apply FunctorEq_Equivalence. Qed.
Next Obligation. intros F F' HF G G' HG O.
  simpl. rewrite HG. rewrite HF. reflexivity.
Qed.
Next Obligation. intros O. simpl. reflexivity. Qed.
Next Obligation. intros O. simpl. reflexivity. Qed.
Next Obligation. intros O. simpl. reflexivity. Qed.
