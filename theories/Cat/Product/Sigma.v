From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.
From Cats Require Export Cat.Product.Indexed.

(** * Products over Dependent Sums of Indices *)

(** * 依赖和索引上的积 *)

Section SigmaProducts.
Context {C : Cat} {I : Type} (J : I → Type).
Context `{HO : !HasLimitsOfShape C (DiscreteCat I)}.
Context (HI : ∀ i, HasLimitsOfShape C (DiscreteCat (J i))).
Context (D : Functor (DiscreteCat (∃ i, J i)) C).

(** Use the chosen product in each fiber of the dependent index family. *)

(** 使用依赖索引族各纤维中的选定积。 *)

Local Instance sigma_fiber_HasLimit (i : I)
  : HasLimit C (DiscreteF (λ j : J i, D (i; j)))
  := @hasLimit C _ (HI i) (DiscreteF (λ j : J i, D (i; j))).

(** The outer family whose values are products over individual index fibers. *)

(** 以各索引纤维中的积为值的外层族。 *)

Definition SigmaProducts (i : I)
  : @Ob C
  := ∏[λ j : J i, D (i; j)].

(** Use the chosen product of the fiber-product objects. *)

(** 使用纤维积对象族的选定积。 *)

Local Instance sigma_outer_HasLimit
  : HasLimit C (DiscreteF SigmaProducts)
  := @hasLimit C _ HO (DiscreteF SigmaProducts).

(** Project from the nested product to a dependent-sum component. *)

(** 从嵌套积投影到依赖和索引的分量。 *)

Definition sigma_product_proj (a : ∃ i, J i)
  : Hom ∏[SigmaProducts] (D a).
Proof.
  destruct a as [i j].
  exact (π∏[λ j : J i, D (i; j)] j ∘ π∏[SigmaProducts] i).
Defined.

(** Nested products satisfy the dependent-sum indexed-product property. *)

(** 嵌套积满足依赖和索引积的性质。 *)

Program Definition SigmaProductLimit
  : HasLimit C D
  :=
  {|Lim := ∏[SigmaProducts]
  ; limit_cone := @DiscreteCone C (∃ i, J i) D _ sigma_product_proj
  |}.
Next Obligation.
  intros X μ.
  pose (p := indexed_pair (D := SigmaProducts)
    (λ i, indexed_pair (D := λ j : J i, D (i; j)) (λ j, μ (i; j)))).
  assert (Hp : ∀ a, sigma_product_proj a ∘ p ≈ μ a).
  { intros [i j]. unfold sigma_product_proj, p.
    cbn beta iota zeta. rewrite comp_assoc.
    transitivity (π∏[λ j : J i, D (i; j)] j ∘
      indexed_pair (D := λ j : J i, D (i; j)) (λ j, μ (i; j))).
    - apply comp_l.
      exact (indexed_product_β (D := SigmaProducts)
        (λ i, indexed_pair (D := λ j : J i, D (i; j)) (λ j, μ (i; j))) i).
    - exact (indexed_product_β (D := λ j : J i, D (i; j)) (λ j, μ (i; j)) j). }
  exists p. refine {|this := _
                   ; that := _
                   |}.
  - exact Hp.
  - intros k Hk.
    apply (indexed_product_hom_ext (D := SigmaProducts)). intros i.
    apply (indexed_product_hom_ext (D := λ j : J i, D (i; j))). intros j.
    rewrite <- !comp_assoc. transitivity (μ (i; j)).
    + exact (Hk (i; j)).
    + symmetry. exact (Hp (i; j)).
Defined.

End SigmaProducts.

(** Choose dependent-sum products from outer and fiberwise products. *)

(** 由外层积及各纤维积选择依赖和索引积。 *)

Program Definition SigmaProductLimits {C : Cat} {I : Type} (J : I → Type)
    `{HO : !HasLimitsOfShape C (DiscreteCat I)}
    (HI : ∀ i, HasLimitsOfShape C (DiscreteCat (J i)))
  : HasLimitsOfShape C (DiscreteCat (∃ i, J i))
  :=
  {|hasLimit D := SigmaProductLimit J HI D
  |}.
