From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural.
From Cats Require Export Cat.Product.Indexed.

(** * Products over Dependent Sums of Indices *)
Section SigmaProducts.
Context {C : Cat} {I : Type} (J : I → Type).
Context `{HO : !HasLimitsOfShape C (DiscreteCat I)}.
Context (HI : ∀ i, HasLimitsOfShape C (DiscreteCat (J i))).
Context (D : Functor (DiscreteCat (∃ i, J i)) C).

Local Instance sigma_fiber_HasLimit (i : I)
  : HasLimit C (DiscreteF (λ j : J i, D (i; j)))
  := @hasLimit C _ (HI i) (DiscreteF (λ j : J i, D (i; j))).

Definition SigmaProducts (i : I)
  : @Ob C
  := Π[λ j : J i, D (i; j)].

Local Instance sigma_outer_HasLimit
  : HasLimit C (DiscreteF SigmaProducts)
  := @hasLimit C _ HO (DiscreteF SigmaProducts).

Definition sigma_product_proj (a : ∃ i, J i)
  : Hom Π[SigmaProducts] (D a).
Proof.
  destruct a as [i j].
  exact (πΠ[λ j : J i, D (i; j)] j ∘ πΠ[SigmaProducts] i).
Defined.

Program Definition SigmaProductLimit
  : HasLimit C D
  := {| Lim := Π[SigmaProducts]
      ; limit_cone := @DiscreteCone C (∃ i, J i) D _ sigma_product_proj |}.
Next Obligation.
  intros X μ.
  pose (p := indexed_pair (D := SigmaProducts)
    (λ i, indexed_pair (D := λ j : J i, D (i; j)) (λ j, μ (i; j)))).
  assert (Hp : ∀ a, sigma_product_proj a ∘ p ≈ μ a).
  { intros [i j]. unfold sigma_product_proj, p.
    cbn beta iota zeta. rewrite comp_assoc.
    transitivity (πΠ[λ j : J i, D (i; j)] j ∘
      indexed_pair (D := λ j : J i, D (i; j)) (λ j, μ (i; j))).
    - apply comp_l.
      exact (indexed_product_β (D := SigmaProducts)
        (λ i, indexed_pair (D := λ j : J i, D (i; j)) (λ j, μ (i; j))) i).
    - exact (indexed_product_β (D := λ j : J i, D (i; j)) (λ j, μ (i; j)) j). }
  exists p. refine {| this := _; that := _ |}.
  - exact Hp.
  - intros k Hk.
    apply (indexed_product_hom_ext (D := SigmaProducts)). intros i.
    apply (indexed_product_hom_ext (D := λ j : J i, D (i; j))). intros j.
    rewrite <- !comp_assoc. transitivity (μ (i; j)).
    + exact (Hk (i; j)).
    + symmetry. exact (Hp (i; j)).
Defined.

End SigmaProducts.

Program Definition SigmaProductLimits {C : Cat} {I : Type} (J : I → Type)
    `{HO : !HasLimitsOfShape C (DiscreteCat I)}
    (HI : ∀ i, HasLimitsOfShape C (DiscreteCat (J i)))
  : HasLimitsOfShape C (DiscreteCat (∃ i, J i))
  := {| hasLimit D := SigmaProductLimit J HI D |}.
