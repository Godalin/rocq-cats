From Cats Require Import
  Instance.Set.Simplicial.Vertex.Cartesian
  Cat.Core
  Cat.Natural
  Cat.Terminal
  Cat.Product.Core
  Cat.Functor.Cartesian
  Cat.Functor.FiniteProducts
  Instance.Set.Product
  Instance.Set.Terminal.

(** * Independent Sizes for Chosen Finite Products *)

Section Levels.
Universes e h o l u q.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < q.

(** The native arrow carrier is strictly above its equality witnesses. *)

Definition Presentations
  : Cat
  := VtxPresentationCat@{o e o h e l h e _ _ _ _ _ _ _ _ _ _}.

Definition NativeProducts
  : HasProduct Presentations
  := VtxPresentationCat_HasProduct.

Definition NativeTerminal
  : HasTerminal Presentations
  := VtxPresentationCat_HasTerminal.

(** The common value equality is below the category-law bound and carrier. *)

Definition low_eq_cartesian
  : @CartFct Presentations
      (FctCat (Δ^op) SetCat@{u o _ _ _ _ _}) NativeTerminal NativeProducts
  := VtxNerveCartF.

(** The same source also permits value equality above its carrier. *)

Definition high_eq_cartesian
  : @CartFct Presentations
      (FctCat (Δ^op) SetCat@{u q _ _ _ _ _}) NativeTerminal NativeProducts
  := VtxNerveCartF.

(** Reverse the native label and arrow carrier/equality profiles. *)

Definition ReversePresentations
  : Cat
  := VtxPresentationCat@{e o e h o l o o _ _ _ _ _ _ _ _ _ _}.

Definition ReverseProducts
  : HasProduct ReversePresentations
  := VtxPresentationCat_HasProduct.

Definition ReverseTerminal
  : HasTerminal ReversePresentations
  := VtxPresentationCat_HasTerminal.

Definition reverse_native_cartesian
  : @CartFct ReversePresentations
      (FctCat (Δ^op) SetCat@{u o _ _ _ _ _}) ReverseTerminal ReverseProducts
  := VtxNerveCartF.

(** The general pointwise structures retain both strict value-size orders. *)

Definition low_eq_pointwise_products
  : HasProduct (FctCat (Δ^op) SetCat@{u o _ _ _ _ _})
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

Definition high_eq_pointwise_products
  : HasProduct (FctCat (Δ^op) SetCat@{u q _ _ _ _ _})
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

Definition low_eq_pointwise_terminal
  : HasTerminal (FctCat (Δ^op) SetCat@{u o _ _ _ _ _})
  := @FctCat_HasTerminal _ _ SetCat_HasTerminal.

Definition high_eq_pointwise_terminal
  : HasTerminal (FctCat (Δ^op) SetCat@{u q _ _ _ _ _})
  := @FctCat_HasTerminal _ _ SetCat_HasTerminal.

(** A probe larger than both value sizes does not resize pointwise values. *)

Context (J : Cat@{q q q q q}).

Definition large_probe_products
  : HasProduct (FctCat J SetCat@{u o _ _ _ _ _})
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

Definition large_probe_terminal
  : HasTerminal (FctCat J SetCat@{u o _ _ _ _ _})
  := @FctCat_HasTerminal _ _ SetCat_HasTerminal.

End Levels.
