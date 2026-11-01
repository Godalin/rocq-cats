From Cats Require Import Cat.Core Cat.Functor Cat.Natural.
From Cats Require Import Instance.Set.Core Instance.Set.Hom Instance.Set.Yoneda.

(** * Representations and Universal Elements

    The source category is arbitrary. All equalities and uniqueness laws
    use the specified hom/setoid equality; mediators remain transparent. *)

Section UniversalElements.
Context {C : Cat} (F : Functor C SetCat).

Definition is_universal_element {X : @Ob C} (u : F X) :=
  ∀ Y (y : F Y), ∃ f : Hom X Y, is_unique (λ f, fmap F f u ≈S y) f.

Theorem universal_element_hom_ext {X Y : @Ob C} {u : F X}
    (Hu : is_universal_element u) (f g : Hom X Y)
  : fmap F f u ≈S fmap F g u → f ≈ g.
Proof.
  intros H. destruct (Hu Y (fmap F g u)) as [h Hh].
  transitivity h.
  - apply (@that _ _ _ _ _ Hh). exact H.
  - symmetry. apply (@that _ _ _ _ _ Hh). reflexivity.
Qed.

Program Definition universal_element_inverse_resp {X : @Ob C} {u : F X}
    (Hu : is_universal_element u) (Y : @Ob C) : F Y →r HomSet X Y :=
  {| func y := (Hu Y y).1 |}.
Next Obligation.
  intros y z H. apply (@that _ _ _ _ _ (Hu Y z).2).
  transitivity y; [exact (@this _ _ _ _ _ (Hu Y y).2) | exact H].
Defined.

Definition universal_element_representation {X : @Ob C} {u : F X}
    (Hu : is_universal_element u) : X ⦂ represents F.
Proof.
  exists (yoneda_func_inv u). intros Y.
  exists (universal_element_inverse_resp Hu Y). split.
  - intros f. symmetry. apply (@that _ _ _ _ _ (Hu Y (fmap F f u)).2). reflexivity.
  - intros y. exact (@this _ _ _ _ _ (Hu Y y).2).
Defined.

Definition universal_element_iso {X Y : @Ob C} {u : F X} {v : F Y}
    (Hu : is_universal_element u) (Hv : is_universal_element v) : X ≅[C] Y.
Proof.
  exists (Hu Y v).1, (Hv X u).1. split.
  - apply (universal_element_hom_ext Hu).
    transitivity (fmap F (Hv X u).1 (fmap F (Hu Y v).1 u)).
    + exact (functor_comp C SetCat F _ _ u).
    + transitivity (fmap F (Hv X u).1 v).
      * apply func_proper. exact (@this _ _ _ _ _ (Hu Y v).2).
      * transitivity u.
        -- exact (@this _ _ _ _ _ (Hv X u).2).
        -- symmetry. exact (functor_id C SetCat F u).
  - apply (universal_element_hom_ext Hv).
    transitivity (fmap F (Hu Y v).1 (fmap F (Hv X u).1 v)).
    + exact (functor_comp C SetCat F _ _ v).
    + transitivity (fmap F (Hu Y v).1 u).
      * apply func_proper. exact (@this _ _ _ _ _ (Hv X u).2).
      * transitivity v.
        -- exact (@this _ _ _ _ _ (Hu Y v).2).
        -- symmetry. exact (functor_id C SetCat F v).
Defined.

End UniversalElements.

Section Representations.
Context {C : Cat} {F : Functor C SetCat}.

Definition representation_generic {X : @Ob C} (R : X ⦂ represents F) : F X :=
  yoneda_func R.1.

Theorem representation_at {X Y : @Ob C} (R : X ⦂ represents F) (f : Hom X Y)
  : R.1 Y f ≈S fmap F f (representation_generic R).
Proof.
  symmetry. exact (yoneda_func_inv_func R.1 Y f).
Defined.

Definition representation_universal {X : @Ob C} (R : X ⦂ represents F)
  : is_universal_element F (representation_generic R).
Proof.
  intros Y y. exists ((R.2 Y).1 y). refine {| this := _; that := _ |}.
  - transitivity (R.1 Y ((R.2 Y).1 y)).
    + symmetry. apply representation_at.
    + exact (snd (R.2 Y).2 y).
  - intros f Hf. transitivity ((R.2 Y).1 (R.1 Y f)).
    + symmetry. exact (fst (R.2 Y).2 f).
    + apply func_proper. transitivity (fmap F f (representation_generic R)).
      * apply representation_at.
      * exact Hf.
Defined.

Theorem represents_iff_universal_element (X : @Ob C)
  : (X ⦂ represents F) ↔ ∃ u : F X, is_universal_element F u.
Proof.
  split.
  - intros R. exists (representation_generic R). apply representation_universal.
  - intros [u Hu]. exact (universal_element_representation F Hu).
Defined.

Theorem representation_round_trip {X : @Ob C} (R : X ⦂ represents F)
  : (universal_element_representation F (representation_universal R)).1 ≈N R.1.
Proof. intros Y f. symmetry. apply representation_at. Qed.

Theorem universal_element_generic {X : @Ob C} {u : F X}
    (Hu : is_universal_element F u)
  : representation_generic (universal_element_representation F Hu) ≈S u.
Proof. exact (functor_id C SetCat F u). Defined.

Definition representation_iso {X Y : @Ob C}
    (R : X ⦂ represents F) (S : Y ⦂ represents F) : X ≅[C] Y :=
  universal_element_iso F (representation_universal R) (representation_universal S).

(** The comparison is unique among maps preserving the universal element,
    rather than among all isomorphisms between the two objects. *)
Theorem representation_iso_universal {X Y : @Ob C}
    (R : X ⦂ represents F) (S : Y ⦂ represents F)
  : is_unique (λ f, fmap F f (representation_generic R) ≈S representation_generic S)
      (representation_iso R S).1.
Proof. exact (representation_universal R Y (representation_generic S)).2. Defined.

End Representations.

(** ** Contravariant Representations

    Use the covariant theory in C^op, with the explicit Hom comparison.
    No duplicate universal-property proof or equality of functors is needed. *)

Definition represents_op {C : Cat} (P : Functor (C^op) SetCat) (X : @Ob C) :=
  Hom(-,X) ≅N P.

Notation "X '⦂' 'represents_op' P" := (represents_op P X) (at level 50).

Definition is_representable_op {C : Cat} (P : Functor (C^op) SetCat) :=
  ∃ X, X ⦂ represents_op P.

Section PresheafRepresentations.
Context {C : Cat} {P : Functor (C^op) SetCat}.

Program Definition represents_op_covariant {X : @Ob C} (R : X ⦂ represents_op P)
  : @represents (C^op) P X := (R.1 ∘Nv (hom_op_nat_iso X).1; _).
Next Obligation.
  exact (nt_comp_v_NatIso R.1 (hom_op_nat_iso X).1 R.2 (hom_op_nat_iso X).2).
Defined.

Definition representation_op_generic {X : @Ob C} (R : X ⦂ represents_op P) : P X :=
  representation_generic (represents_op_covariant R).

Theorem representation_op_at {X Y : @Ob C} (R : X ⦂ represents_op P) (f : Hom Y X)
  : R.1 Y f ≈S fmap P f (representation_op_generic R).
Proof. exact (representation_at (represents_op_covariant R) f). Defined.

Definition representation_op_universal {X : @Ob C} (R : X ⦂ represents_op P)
  : is_universal_element P (representation_op_generic R) :=
  representation_universal (represents_op_covariant R).

Definition universal_element_representation_op {X : @Ob C} {u : P X}
    (Hu : is_universal_element P u) : X ⦂ represents_op P :=
  transitivity (symmetry (hom_op_nat_iso X)) (universal_element_representation P Hu).

Theorem represents_op_iff_universal_element (X : @Ob C)
  : (X ⦂ represents_op P) ↔ ∃ u : P X, is_universal_element P u.
Proof.
  split.
  - intros R. exists (representation_op_generic R). apply representation_op_universal.
  - intros [u Hu]. exact (universal_element_representation_op Hu).
Defined.

Theorem representation_op_round_trip {X : @Ob C} (R : X ⦂ represents_op P)
  : (universal_element_representation_op (representation_op_universal R)).1 ≈N R.1.
Proof. intros Y f. symmetry. apply representation_op_at. Qed.

Theorem universal_element_op_generic {X : @Ob C} {u : P X}
    (Hu : is_universal_element P u)
  : representation_op_generic (universal_element_representation_op Hu) ≈S u.
Proof. exact (functor_id (C^op) SetCat P u). Defined.

Definition representation_op_iso {X Y : @Ob C}
    (R : X ⦂ represents_op P) (S : Y ⦂ represents_op P) : X ≅[C] Y.
Proof.
  pose (I := representation_iso (represents_op_covariant R) (represents_op_covariant S)).
  exists I.2.1, I.1. split; [exact (fst I.2.2) | exact (snd I.2.2)].
Defined.

Theorem representation_op_iso_universal {X Y : @Ob C}
    (R : X ⦂ represents_op P) (S : Y ⦂ represents_op P)
  : is_unique (λ f, fmap P f (representation_op_generic S) ≈S representation_op_generic R)
      (representation_op_iso R S).1.
Proof. exact (representation_op_universal S X (representation_op_generic R)).2. Defined.

End PresheafRepresentations.
