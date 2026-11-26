From Cats Require Import
  Instance.Set.Simplicial.Vertex.Cartesian
  Instance.Set.Simplicial.Vertex.Monoid
  Instance.Bool.Group
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal
  Cat.Product.Core
  Cat.Functor.Cartesian
  Cat.Functor.FiniteProducts
  Instance.Set.Product.

Local Open Scope nat_scope.

(** * Computing through Chosen Finite Products and Their Preservation *)

Definition SmallPresentations
  : Cat
  := VtxPresentationCat@{Set Set Set Set Set Set Set Set
      _ _ _ _ _ _ _ _ _ _}.

Definition SmallProducts
  : HasProduct SmallPresentations
  := VtxPresentationCat_HasProduct.

Definition SmallTerminal
  : HasTerminal SmallPresentations
  := VtxPresentationCat_HasTerminal.

Definition SmallPointwiseProducts
  : HasProduct (FctCat (Δ^op) SetCat@{Set Set _ _ _ _ _})
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

(** The bundle's coercion exposes the original computational nerve. *)

Definition SmallNerve
  : @CartFct SmallPresentations
      (FctCat (Δ^op) SetCat@{Set Set _ _ _ _ _}) SmallTerminal SmallProducts
  := VtxNerveCartF.

(** The original full-faithfulness interface remains usable by coercion. *)

Example cartesian_full_faithfulness
  : is_fully_faithful SmallNerve.
Proof. exact vertex_nerve_fully_faithful. Qed.

Definition BooleanPresentation
  : VtxPresentation@{Set Set Set Set Set Set Set Set}
  := VtxPresentationOf (MonoidObjF BoolS_Monoid).

(** The actual source product mediator retains both nonidentity arrows. *)

Example chosen_pair_computes
  : let P := BooleanPresentation in
    fmap (@pair SmallPresentations SmallProducts P P P
      (@Cats.Cat.Core.id SmallPresentations P)
      (@Cats.Cat.Core.id SmallPresentations P))
      (true : (@Hom (VtxCat P)) tt tt) = (true, true).
Proof. reflexivity. Qed.

(** Applying the bundled nerve to the mediator preserves its two edges. *)

Example nerve_pair_computes
  : let P := BooleanPresentation in
    let edge := △₁[P; tt; tt] true in
    fmap (lower (fmap SmallNerve
      (@pair SmallPresentations SmallProducts P P P
        (@Cats.Cat.Core.id SmallPresentations P)
        (@Cats.Cat.Core.id SmallPresentations P)) 1 edge))
      (ordinal_step fin_first) = (true, true).
Proof. reflexivity. Qed.

(** The generic inverse comparison uses the stored preservation witness;
    it computes even when the two boolean arrows are different. *)

Example stored_product_inverse_computes
  : let P := BooleanPresentation in
    let inverse := @fct_product_inv _ _ SmallNerve
      SmallTerminal SmallProducts SmallPointwiseProducts
      (isCartF SmallNerve) P P in
    fmap (lower (inverse 1 (△₁[P; tt; tt] true, △₁[P; tt; tt] false)))
      (ordinal_step fin_first) = (true, false).
Proof. reflexivity. Qed.

(** The stored terminal universal arrow contains an actual constant diagram. *)

Example stored_terminal_arrow_computes
  : let P := BooleanPresentation in
    let terminal := @fct_terminal _ _ SmallNerve
      SmallTerminal SmallProducts (isCartF SmallNerve) in
    lower ((terminal (SmallNerve P)).1 1 (△₁[P; tt; tt] true)) fin_first = tt.
Proof. reflexivity. Qed.
