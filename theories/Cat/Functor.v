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

(** ** Faithful and Full Functors

    Comparisons use the source and target categories' morphism equivalences.
    Fullness retains a preimage witness in [Type] for each target morphism. *)

Definition is_faithful {C D : Cat} (F : Functor C D) :=
  ∀ X Y (f g : Hom X Y), fmap F f ≈ fmap F g → f ≈ g.

Definition is_full {C D : Cat} (F : Functor C D) :=
  ∀ X Y (g : Hom (F X) (F Y)), ∃ f : Hom X Y, fmap F f ≈ g.

Definition is_fully_faithful {C D : Cat} (F : Functor C D) :=
  is_full F ∧ is_faithful F.

Definition functor_is_iso {C D : Cat} (F : Functor C D)
    {X Y : @Ob C} (f : Hom X Y) (Hf : is_iso f) : is_iso (fmap F f).
Proof.
  exists (fmap F Hf.1). split;
    unfold is_linv_of, is_rinv_of in *;
    rewrite <- functor_comp;
    [rewrite (fst Hf.2) | rewrite (snd Hf.2)]; apply functor_id.
Defined.



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

(** ** Fixing One Argument of a Functor from a Product Category *)

Section PartialFunctor.
Context {C D E : Cat}.

(** Vary the first argument, keeping the second fixed. *)
Program Definition π1F (F : Functor (C ×C D) E) (d : @Ob D) : Functor C E :=
  {| F0 c := F (c, d)
   ; F1 X Y f := fmap F (X := (X, d)) (Y := (Y, d)) (f, id) |}.
Next Obligation.
  intros u v Huv. apply functor_fmap_proper. split; cato.
Qed.
Next Obligation. apply functor_id. Qed.
Next Obligation.
  rewrite <- functor_comp. apply functor_fmap_proper. split; cato.
Qed.

(** Vary the second argument, keeping the first fixed. *)
Program Definition π2F (F : Functor (C ×C D) E) (c : @Ob C) : Functor D E :=
  {| F0 d := F (c, d)
   ; F1 X Y f := fmap F (X := (c, X)) (Y := (c, Y)) (id, f) |}.
Next Obligation.
  intros u v Huv. apply functor_fmap_proper. split; cato.
Qed.
Next Obligation. apply functor_id. Qed.
Next Obligation.
  rewrite <- functor_comp. apply functor_fmap_proper. split; cato.
Qed.

End PartialFunctor.

Infix "∘F" := CompF
  (at level 40) : cat_scope.

Lemma fmap_eq_to_hom {C D : Cat} (F : Functor C D)
    {X Y : @Ob C} (p : X = Y)
  : fmap F (eq_to_hom p) ≈ eq_to_hom (f_equal F p).
Proof. destruct p. simpl. apply functor_id. Qed.

(** ** Opposite Functors

    Taking opposites reverses arrows in both categories. Double opposition
    is compared by explicit identity-on-objects-and-morphisms functors, without
    requiring equality of category records or their law proofs. *)

Program Definition OpF {C D : Cat} (F : Functor C D)
  : Functor (C ^op) (D ^op) :=
  {| F0 X := F X
   ; F1 X Y f := fmap F f |}.
Next Obligation. intros u v Huv. apply functor_fmap_proper. exact Huv. Qed.
Next Obligation. apply functor_id. Qed.
Next Obligation. apply functor_comp. Qed.

Notation "F '^opF'" := (OpF F) (at level 35) : cat_scope.

Program Definition ToDoubleOpF {C : Cat} : Functor C (C ^op ^op) :=
  {| F0 X := X; F1 X Y f := f |}.
Next Obligation. intros f g Hfg. exact Hfg. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Program Definition FromDoubleOpF {C : Cat} : Functor (C ^op ^op) C :=
  {| F0 X := X; F1 X Y f := f |}.
Next Obligation. intros f g Hfg. exact Hfg. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
