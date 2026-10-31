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
  destruct Hf as [fi [Hl Hr]]. exists (fmap F fi). split;
    unfold is_linv_of, is_rinv_of in *;
    rewrite <- functor_comp; [rewrite Hl | rewrite Hr]; apply functor_id.
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

Global Instance π1F_proper {C D E : Cat} (d : @Ob D)
  : Proper (FunctorEq ==> FunctorEq)
      (λ F : Functor (C ×C D) E, π1F F d).
Proof.
  intros F G [p Hp]. exists (λ c, p (c, d)).
  intros X Y f. exact (Hp (X, d) (Y, d) (f, id)).
Qed.

Global Instance π2F_proper {C D E : Cat} (c : @Ob C)
  : Proper (FunctorEq ==> FunctorEq)
      (λ F : Functor (C ×C D) E, π2F F c).
Proof.
  intros F G [p Hp]. exists (λ d, p (c, d)).
  intros X Y f. exact (Hp (c, X) (c, Y) (id, f)).
Qed.



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

Global Instance OpF_proper {C D : Cat}
  : Proper (FunctorEq ==> FunctorEq) (@OpF C D).
Proof.
  intros F G [p Hp]. exists p. intros X Y f. simpl.
  rewrite !eq_to_hom_op.
  rewrite <- (comp_id_l (fmap F f)).
  rewrite <- (eq_to_hom_inv_l (p X)).
  rewrite (comp_assoc _ _ (fmap F f)), (Hp Y X f).
  rewrite !comp_assoc, eq_to_hom_inv_r.
  rewrite comp_id_r. reflexivity.
Qed.

Theorem OpF_id {C : Cat} : OpF (@IdF C) =F (@IdF (C ^op)).
Proof. exists (λ X, eq_refl). intros X Y f. simpl. carw. Qed.

Theorem OpF_comp {C D E : Cat} (G : Functor D E) (F : Functor C D)
  : OpF (G ∘F F) =F (OpF G ∘F OpF F).
Proof. exists (λ X, eq_refl). intros X Y f. simpl. carw. Qed.

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

Definition op_involution (C : Cat) : (C ^op ^op) ≅[CatCat] C.
Proof.
  exists FromDoubleOpF, ToDoubleOpF. split;
    exists (λ X, eq_refl); intros X Y f; simpl; carw.
Defined.

Theorem OpF_involution {C D : Cat} (F : Functor C D)
  : FromDoubleOpF ∘F (OpF (OpF F) ∘F ToDoubleOpF) =F F.
Proof. exists (λ X, eq_refl). intros X Y f. simpl. carw. Qed.

Program Definition OpCatF : Functor CatCat CatCat :=
  {| F0 := op; F1 C D F := OpF F |}.
Next Obligation. apply OpF_id. Qed.
Next Obligation. apply OpF_comp. Qed.
