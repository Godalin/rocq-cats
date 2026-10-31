From Cats Require Import Cat.Core.



(** * Functor *)

Record Functor (C D : Cat) :=
  { F0 :> @Ob C → @Ob D
  ; F1 {X Y : @Ob C} : Hom X Y → Hom (F0 X) (F0 Y)

  ; functor_fmap_proper {X Y}
    :: Proper (@HomEq[X, Y] ==> @HomEq[F0 X, F0 Y]) F1

  ; functor_id {X}
    : F1 (@id X) ≈ @id (F0 X)

  ; functor_comp {X Y Z} (f : Hom Y Z) (g : Hom X Y)
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
  rewrite functor_fmap_proper. reflexivity.
  rewrite functor_fmap_proper. reflexivity. auto.
Qed.
Next Obligation.
  repeat rewrite functor_id. reflexivity.
Qed.
Next Obligation.
  repeat rewrite functor_comp. reflexivity.
Qed.

(** Equality between Functors.

    Object equalities induce the connecting morphisms in the comparison
    square. Its commutativity compares the morphism actions up to [HomEq].
    The object equalities are retained as data; no equality between them or
    between functor-law proofs is required. *)

Definition FunctorEq {C D : Cat} (F G : Functor C D)
  := ∃ p : ∀ X, F X = G X,
       ∀ X Y (f : Hom X Y),
         eq_to_hom (p Y) ∘ fmap F f ≈ fmap G f ∘ eq_to_hom (p X).

Instance FunctorEq_Equivalence {C D}
  : Equivalence (@FunctorEq C D).
Proof. split.
  - intros F. exists (λ X, eq_refl (F X)). intros X Y f. simpl. carw.
  - intros F G [p Hp]. exists (λ X, eq_sym (p X)). intros X Y f.
    rewrite <- (comp_id_r (fmap G f)).
    rewrite <- (eq_to_hom_inv_r (p X)).
    rewrite <- (comp_assoc (fmap G f)).
    rewrite <- Hp.
    repeat rewrite <- comp_assoc.
    rewrite eq_to_hom_inv_l, comp_id_l. reflexivity.
  - intros F G H [p Hp] [q Hq].
    exists (λ X, eq_trans (p X) (q X)). intros X Y f.
    rewrite !eq_to_hom_comp.
    rewrite comp_assoc, Hp.
    rewrite <- comp_assoc, Hq.
    rewrite comp_assoc. reflexivity.
Qed.

Infix "∘F" := CompF
  (at level 40) : cat_scope.

Infix "=F" := FunctorEq
  (at level 50) : cat_scope.



Lemma fmap_eq_to_hom {C D : Cat} (F : Functor C D)
    {X Y : @Ob C} (p : X = Y)
  : fmap F (eq_to_hom p) ≈ eq_to_hom (f_equal F p).
Proof. destruct p. simpl. apply functor_id. Qed.

Global Instance CompF_proper {C D E : Cat}
  : Proper (FunctorEq ==> FunctorEq ==> FunctorEq) (@CompF C D E).
Proof.
  intros G G' [q Hq] F F' [p Hp].
  exists (λ X, eq_trans (f_equal G (p X)) (q (F' X))).
  intros X Y f. simpl.
  rewrite !eq_to_hom_comp, <- !fmap_eq_to_hom.
  rewrite comp_assoc, <- functor_comp.
  rewrite Hp, functor_comp.
  rewrite <- comp_assoc, Hq.
  rewrite comp_assoc. reflexivity.
Qed.



(** ** Category of small categories *)

Program Instance CatCat : Cat :=
  { Ob := Cat
  ; Hom C D := Functor C D
  ; HomEq _ _ := FunctorEq
  ; id _ := IdF
  ; comp _ _ _ := CompF
  }.
Next Obligation.
  exists (λ A, eq_refl). intros A B u. simpl. carw.
Qed.
Next Obligation.
  exists (λ A, eq_refl). intros A B u. simpl. carw.
Qed.
Next Obligation.
  exists (λ A, eq_refl). intros A B u. simpl. carw.
Qed.
