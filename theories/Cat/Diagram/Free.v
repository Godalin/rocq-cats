From Cats Require Export Cat.Free Cat.Diagram.
From Cats Require Import Cat.Core Cat.Functor Cat.Natural.

(** * Cones Specified on Generators *)
Definition FreeCone {G : Graph} {C : Cat} {D : Functor (FreeCat G) C}
    {X : @Ob C} (κ : ∀ x, Hom X (D x))
    (Hκ : ∀ x y (e : Edge x y), fmap D (path_edge e) ∘ κ x ≈ κ y)
  : X ⇒Δ D.
Proof.
  refine (@FreeN G C (ConstF (FreeCat G) X) D κ _).
  intros x y e. cbn. rewrite comp_id_r. symmetry. apply Hκ.
Defined.

Lemma free_cone_edge {G : Graph} {C : Cat} {D : Functor (FreeCat G) C}
    {X : @Ob C} (κ : X ⇒Δ D) {x y} (e : Edge x y)
  : fmap D (path_edge e) ∘ κ x ≈ κ y.
Proof.
  pose proof (nt_naturality κ (path_edge e)) as H.
  cbn in H. rewrite comp_id_r in H. symmetry. exact H.
Qed.
