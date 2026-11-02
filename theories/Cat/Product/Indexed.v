From Cats Require Import Cat.Core Cat.Functor Cat.Natural.
From Cats Require Export Cat.Limit Cat.Diagram.Discrete.

(** * Indexed Products as Discrete Limits

    The chosen structure is [HasLimit C (DiscreteF D)]. No second copy of
    its universal property, mediator, or coherence laws is stored. *)
Notation "'Π[' D ']'" := (Lim (DiscreteF D)) : ob_scope.

Section IndexedProduct.
Context {C : Cat} {I : Type} {D : I → @Ob C}
    `{HP : !HasLimit C (DiscreteF D)}.

Definition indexed_proj (i : I) : Hom Π[D] (D i) := πlim[DiscreteF D] i.

Definition indexed_pair {X : @Ob C} (κ : ∀ i, Hom X (D i)) : Hom X Π[D] :=
  @limit_lift (DiscreteCat I) C (DiscreteF D) HP X
    (@DiscreteCone C I (DiscreteF D) X κ).

Lemma indexed_product_β {X : @Ob C} (κ : ∀ i, Hom X (D i)) (i : I)
  : indexed_proj i ∘ indexed_pair κ ≈ κ i.
Proof.
  exact (@limit_β (DiscreteCat I) C (DiscreteF D) HP X
    (@DiscreteCone C I (DiscreteF D) X κ) i).
Qed.

Lemma indexed_product_η {X : @Ob C} (f : Hom X Π[D])
  : indexed_pair (λ i, indexed_proj i ∘ f) ≈ f.
Proof.
  transitivity (lim⟨πlim[DiscreteF D] ∘Cone f⟩).
  - apply limit_lift_proper. intros i. reflexivity.
  - apply limit_η.
Qed.

Global Instance indexed_pair_proper {X : @Ob C}
  : Proper ((λ κ μ : ∀ i, Hom X (D i), ∀ i, κ i ≈ μ i) ==>
      @HomEq C X Π[D]) indexed_pair.
Proof. intros κ μ H. apply limit_lift_proper. exact H. Qed.

Lemma indexed_product_comp {X Y : @Ob C} (κ : ∀ i, Hom X (D i)) (f : Hom Y X)
  : indexed_pair κ ∘ f ≈ indexed_pair (λ i, κ i ∘ f).
Proof.
  unfold indexed_pair. rewrite <- limit_lift_comp.
  apply limit_lift_proper. intros i. reflexivity.
Qed.

Theorem indexed_product_hom_ext {X : @Ob C} (f g : Hom X Π[D])
    (H : ∀ i, indexed_proj i ∘ f ≈ indexed_proj i ∘ g) : f ≈ g.
Proof.
  rewrite <- (indexed_product_η f), <- (indexed_product_η g).
  apply indexed_pair_proper. exact H.
Qed.

End IndexedProduct.

Notation "'πΠ[' D ']'" := (indexed_proj (D := D)) : hom_scope.
Notation "'Π⟨' κ '⟩'" := (indexed_pair κ) : hom_scope.
