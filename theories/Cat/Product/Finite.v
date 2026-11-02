From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Terminal
  Cat.Product.
From Cats.Set Require Export Finite.
From Cats Require Export Cat.Product.Indexed.

(** * Finite Products from Terminal Objects and Binary Products *)
Section FiniteProducts.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}.

Fixpoint FiniteProduct {n : nat} (D : Fin n → @Ob C)
  : @Ob C
  := match n as m return (Fin m → @Ob C) → @Ob C with
  | O => λ _, 1
  | S m => λ D, (D fin_first × FiniteProduct (λ i : Fin m, D (fin_next i)))%ob
  end D.

Fixpoint finite_product_proj {n : nat} (D : Fin n → @Ob C) (i : Fin n)
  : Hom (FiniteProduct D) (D i).
Proof.
  destruct n as [|n]; [destruct i |].
  destruct i as [[] | i]; cbn.
  - exact π1.
  - exact (@finite_product_proj n (λ j : Fin n, D (fin_next j)) i ∘ π2).
Defined.

Fixpoint finite_product_pair {n : nat} (D : Fin n → @Ob C) {X : @Ob C}
    (κ : ∀ i, Hom X (D i))
  : Hom X (FiniteProduct D)
  := match n as m return ∀ D : Fin m → @Ob C,
      (∀ i, Hom X (D i)) → Hom X (FiniteProduct D) with
  | O => λ D κ, !
  | S m => λ D κ, ⟨κ fin_first,
      finite_product_pair (λ i : Fin m, D (fin_next i)) (λ i, κ (fin_next i))⟩
  end D κ.

Lemma finite_product_β {n : nat} (D : Fin n → @Ob C) {X : @Ob C}
    (κ : ∀ i, Hom X (D i)) (i : Fin n)
  : finite_product_proj D i ∘ finite_product_pair D κ ≈ κ i.
Proof.
  induction n as [|n IH] in D, κ, i |- *; [destruct i |].
  destruct i as [[] | i]; cbn.
  - apply product_β1.
  - rewrite comp_assoc, product_β2.
    exact (IH (λ j, D (fin_next j)) (λ j, κ (fin_next j)) i).
Qed.

Theorem finite_product_hom_ext {n : nat} (D : Fin n → @Ob C) {X : @Ob C}
    (f g : Hom X (FiniteProduct D))
    (H : ∀ i, finite_product_proj D i ∘ f ≈ finite_product_proj D i ∘ g)
  : f ≈ g.
Proof.
  induction n as [|n IH] in D, f, g, H |- *.
  - transitivity (@term C HT X); [apply term_η | symmetry; apply term_η].
  - rewrite (product_η f), (product_η g). apply product_pair_proper.
    + exact (H fin_first).
    + apply (IH (λ i, D (fin_next i)) (π2 ∘ f) (π2 ∘ g)).
      intros i. rewrite <- !comp_assoc. exact (H (fin_next i)).
Qed.

(** The result is the existing indexed-product structure. The construction
    works for every functor on the finite discrete shape. *)
Program Definition FiniteProductLimit {n : nat}
    (D : Functor (DiscreteCat (Fin n)) C)
  : HasLimit C D
  := {| Lim := FiniteProduct (λ i, D i)
      ; limit_cone := @DiscreteCone C (Fin n) D _ (finite_product_proj (λ i, D i)) |}.
Next Obligation.
  intros X μ. exists (finite_product_pair (λ i, D i) (λ i, μ i)).
  refine {| this := _; that := _ |}.
  - intros i. apply finite_product_β.
  - intros k Hk. apply finite_product_hom_ext. intros i.
    transitivity (μ i); [exact (Hk i) | symmetry; apply finite_product_β].
Defined.

Program Definition FiniteProductLimits (n : nat)
  : HasLimitsOfShape C (DiscreteCat (Fin n))
  := {| hasLimit := FiniteProductLimit |}.

Global Instance finite_product_pair_proper {n : nat} (D : Fin n → @Ob C)
    {X : @Ob C}
  : Proper ((λ κ μ : ∀ i, Hom X (D i), ∀ i, κ i ≈ μ i) ==>
      @HomEq C X (FiniteProduct D)) (finite_product_pair D).
Proof.
  exact (@indexed_pair_proper C (Fin n) D (FiniteProductLimit (DiscreteF D)) X).
Qed.

End FiniteProducts.
