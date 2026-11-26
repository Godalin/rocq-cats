From Cats Require Import
  Cat.Core
  Cat.Preorder
  Cat.Terminal
  Cat.Product.Core
  Cat.Functor.Core
  Cat.Functor.Cartesian
  Cat.Functor.Codiscrete
  Cat.Natural
  Cat.Cartesian.Core
  Cat.Cartesian.Construction
  Cat.Cartesian.Category
  Cat.Groupoid.Core
  Cat.Groupoid.Preorder
  Cat.Groupoid.CoreGpd
  Cat.Groupoid.Category.

(** * Universes of Structured Categories

    The constructions check self-membership at distinct universe instances.
    Exercise categorical clients and computation of selected product and
    inverse witnesses here. *)

(** ** Stored Cartesian Preservation

    Packing retains the supplied witness, and instance search on an
    abstract bundle selects its projection for the same source choices. *)

Section StoredPreservation.
Context {C D : Cat} (TC : HasTerminal C) (PC : HasProduct C).

Example cart_fct_stored_witness (F : Fct C D) (H : IsCartF F TC PC)
  : isCartF (MakeCartFct F H) = H
  := eq_refl.

Example cart_fct_inferred_witness (G : @CartFct C D TC PC)
  : (ltac:(typeclasses eauto) : IsCartF G TC PC) = isCartF G
  := eq_refl.

End StoredPreservation.

(** ** Cartesian Clients

    The stored product choice supplies ordinary pairing and its laws.
    The ambient category is explicit because the objects are bundles. *)

Section CartesianClients.
Context (S C D : @Ob CartCatCartCat)
    (F F' : (@Hom CartCatCartCat) S C) (G : (@Hom CartCatCartCat) S D).
Let HP := hasProduct CartCatCartCat.
Local Existing Instance HP.

Definition universe_pair
  : (@Hom CartCatCartCat) S (C × D)
  := ⟨F,G⟩.

Example universe_pair_rewrites (H : F ≈ F')
  : ⟨F,G⟩ ≈ ⟨F',G⟩.
Proof. rewrite H. reflexivity. Qed.

Example universe_pair_first
  : π1 ∘ universe_pair ≈ F.
Proof. apply product_β1. Qed.

Example universe_pair_second
  : π2 ∘ universe_pair ≈ G.
Proof. apply product_β2. Qed.

Example universe_pair_unique (K : (@Hom CartCatCartCat) S (C × D))
    (H1 : π1 ∘ K ≈ F) (H2 : π2 ∘ K ≈ G)
  : K ≈ universe_pair.
Proof. apply (product_pair_unique S F G). split; assumption. Qed.

End CartesianClients.

(** ** Stored Choices and Computation

    Two codiscrete bundles share a category but choose different terminal
    and product objects. Pairing must keep each component's choice. *)

Module CartesianComputation.
Definition Left
  : CartCat
  := CodiscreteCart bool false.

Definition Right
  : CartCat
  := CodiscreteCart bool true.

Program Definition Change
  : CartFctS Left Right
  := MakeCartFct (@IdF Left)
    {|fct_terminal := _
    ; fct_product X Y := _
    |}.
Next Obligation.
  intro X. exists tt. split; [exact I |]. intros f _. exact tt.
Defined.
Next Obligation.
  intros Z f g. exists tt. split.
  - split; exact tt.
  - intros h _. exact tt.
Defined.

Definition ChangePair
  : (@Hom CartCatCartCat) Left (ProdCart Left Right)
  := @Cats.Cat.Product.Core.pair CartCatCartCat
    (hasProduct CartCatCartCat) Left Right Left
    (IdCartF Left (hasTerminal Left) (hasProduct Left)) Change.

Example terminal_choices_compute
  : @Term (ProdCart Left Right) (hasTerminal (ProdCart Left Right))
      = (false,true).
Proof. reflexivity. Qed.

Example product_choices_compute
  : @Prod (ProdCart Left Right) (hasProduct (ProdCart Left Right))
      (true,false) (false,true) = (false,true).
Proof. reflexivity. Qed.

Example mediator_object_computes
  : ChangePair true = (true,true).
Proof. reflexivity. Qed.

Example mediator_arrow_computes
  : fmap ChangePair (X := false) (Y := true) tt = (tt,tt).
Proof. reflexivity. Qed.

Example terminal_fct_computes
  : (@term CartCatCartCat (hasTerminal CartCatCartCat) Left) true = tt.
Proof. reflexivity. Qed.

End CartesianComputation.

(** ** Equivalences and Their Selected Inverses

    A nontrivial object swap in a codiscrete groupoid is an arrow of the
    groupoid universe. Its chosen quasi-inverse must remain executable. *)

Module GroupoidComputation.
Definition Two
  : Gpd
  := CodiscreteGpd bool.

Program Definition Swap
  : Fct Two Two
  :=
  {|fobj := negb
  ; fmap X Y f := tt
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros f g H. exact tt. Qed.
Next Obligation. exact tt. Qed.
Next Obligation. exact tt. Qed.

Definition SwapEquivalence
  : (@Hom GpdGpd) Two Two
  := (Swap; (Swap;
      (CodiscreteNatIso (Swap ∘F Swap) IdF,
       CodiscreteNatIso (Swap ∘F Swap) IdF))).

Example equivalence_computes
  : (fmap GpdForgetF SwapEquivalence) false = true.
Proof. reflexivity. Qed.

Example inverse_computes
  : (fmap GpdForgetF (gpd_inv SwapEquivalence)) true = false.
Proof. reflexivity. Qed.

Example inverse_law
  : gpd_inv SwapEquivalence ∘ SwapEquivalence ≈ id.
Proof. apply gpd_inv_l. Qed.

Example inverse_rewrites
  : SwapEquivalence ∘ (gpd_inv SwapEquivalence ∘ SwapEquivalence)
      ≈ SwapEquivalence.
Proof. rewrite gpd_inv_l. apply comp_id_r. Qed.

End GroupoidComputation.

(** ** Independent Sizes

    Both strict orders between hom carriers and equality witnesses are
    accepted; law bounds are larger and object bounds remain independent. *)

Section IndependentSizes.
Universes o h p l.
Constraint h < p.
Constraint p < l.
Constraint l < o.
Context (C : CartCat@{l o h p l}) (D : CartCat@{l o p h l})
    (G : Gpd@{o h p l}) (H : Gpd@{o p h l}).

Definition mixed_size_product
  : CartCat
  := ProdCart C D.

Definition high_equality_cartesian_object
  : @Ob CartCatCartCat
  := C.

Definition low_equality_cartesian_object
  : @Ob CartCatCartCat
  := D.

Definition high_equality_groupoid_object
  : @Ob GpdGpd
  := G.

Definition low_equality_groupoid_object
  : @Ob GpdGpd
  := H.

End IndependentSizes.
