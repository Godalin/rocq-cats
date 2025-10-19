From Cats Require Import Cat.Core.
From Cats Require Import Cat.Set.



(** * Functor *)

Record Functor (C D : Cat) :=
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

Program Canonical IdF {C : Cat} : Functor C C :=
  {|F0 X := X
  ; F1 _ _ f := f
  |}.
Next Obligation. intros x y. auto. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Program Canonical CompF {C D E : Cat}
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
Next Obligation. intros F F' HF G G' HG O.
  simpl. rewrite HG. rewrite HF. reflexivity.
Qed.
Next Obligation. intros O. simpl. reflexivity. Qed.
Next Obligation. intros O. simpl. reflexivity. Qed.
Next Obligation. intros O. simpl. reflexivity. Qed.



(** ** Hom-Functor *)

Definition ℎ1 {C : Cat} (X : Ob) := λ Y, Hom X Y.
Definition ℎ2 {C : Cat} (X : Ob) := λ Y, Hom Y X.

Program Definition ℎ1F {C : Cat} (X : Ob) : Functor C SetCat :=
  {|F0 := ℎ1 X
  ; F1 Y Y' (f : Hom Y Y') := f _*
  |}.
Next Obligation. intros f f' Hf g. simpl. rewrite Hf. cato. Qed.
Next Obligation. intros f. simpl. cato. Qed.
Next Obligation. intros x. simpl. apply axiom_comp_assoc. Qed.

Notation "'Hom(' X  ',-)'" := (ℎ1F X).

Program Definition ℎ2F {C : Cat} (X : Ob)
  : Functor (op C) SetCat :=
  {|F0 := ℎ2 X
  ; F1 Y Y' (f : (@Hom C) Y' Y) := f ^*
  |}.
Next Obligation. intros f f' Hf g. simpl. rewrite Hf. cato. Qed.
Next Obligation. intros f. simpl. cato. Qed.
Next Obligation. intros x. simpl. cacl. Qed.

Notation "'Hom(-,'  X ')'" := (ℎ2F X).

Program Canonical bi_comp {C : Cat} {X' X Y Y' : @Ob C}
    (f : (@Hom op C) X X') (g : Hom Y Y')
  : (Hom X Y) →r (Hom X' Y')
  := {|func := λ h, g ∘ h ∘ f |}.
Next Obligation. intros h h' Hh. rewrite Hh. cato. Qed.

Program Definition HomF {C : Cat}
  : Functor (op C ×C C) SetCat :=
  {|F0 X := (@Hom C) (fst X) (snd X)
  ; F1 _ _ f := bi_comp (fst f) (snd f)
  |}.
Next Obligation. simpl. intros [f g] [f' g'] [Hf Hg].
  simpl. intros h. simpl.
  rewrite Hf, Hg. reflexivity.
Qed.
Next Obligation. simpl. intros h. simpl; carw. Qed.
Next Obligation. simpl. intros g. simpl. repeat cacr. Qed.
