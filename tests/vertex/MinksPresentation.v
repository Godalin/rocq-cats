From Cats Require Import
  Instance.Set.Vertex.FiniteProducts
  Cat.Preorder
  Cat.Diagram.Core
  Cat.Product.Core
  Cat.Terminal.

(** A label set has no implicit selected presentation. *)

Section NoDefaultAction.
Context (X : SetC).

Fail Definition unchosen_action
  : HasVtxAction X
  := ltac:(typeclasses eauto).

End NoDefaultAction.

Program Definition FalseAction
  : HasVtxAction@{Set Set Set Set Set Set Set Set} UnitS@{Set Set}
  :=
  {|vertex_ambient := CodiscreteCat@{Set Set Set Set} bool
  ; vertex_action := ConstF (EqGpd UnitS@{Set Set})
      (C := CodiscreteCat@{Set Set Set Set} bool) false
  |}.

Program Definition TrueAction
  : HasVtxAction@{Set Set Set Set Set Set Set Set} UnitS@{Set Set}
  :=
  {|vertex_ambient := CodiscreteCat@{Set Set Set Set} bool
  ; vertex_action := ConstF (EqGpd UnitS@{Set Set})
      (C := CodiscreteCat@{Set Set Set Set} bool) true
  |}.

Program Definition UnitAmbientAction
  : HasVtxAction@{Set Set Set Set Set Set Set Set} UnitS@{Set Set}
  :=
  {|vertex_ambient := CodiscreteCat@{Set Set Set Set} unit
  ; vertex_action := ConstF (EqGpd UnitS@{Set Set})
      (C := CodiscreteCat@{Set Set Set Set} unit) tt
  |}.

Definition FalsePresentation
  : VtxPresentation@{Set Set Set Set Set Set Set Set}
  := MakeVtxPresentation UnitS FalseAction.

Definition TruePresentation
  : VtxPresentation@{Set Set Set Set Set Set Set Set}
  := MakeVtxPresentation UnitS TrueAction.

(** The native label parent and the action remain different, coherent
    views of the same stored data. No category-to-type coercion is added. *)

Definition original_label
  : FalsePresentation
  := tt.

Example labels_kept
  : VtxPresentationToSetC FalsePresentation = UnitS@{Set Set}
  := eq_refl.

Example native_label_parent_agrees
  : (VtxPresentationToSetCCarrier FalsePresentation : SetC) =
      VtxPresentationToSetC FalsePresentation
  := eq_refl.

Example component_kept
  : hasVtxAction FalsePresentation = FalseAction
  := eq_refl.

Example ambient_kept
  : vertex_ambient FalsePresentation = CodiscreteCat@{Set Set Set Set} bool
  := eq_refl.

Example action_kept
  : vertex_action FalsePresentation = vertex_action FalseAction
  := eq_refl.

Example callable_view_computes
  : FalsePresentation original_label = false
  := eq_refl.

Section CompetingAction.
Local Existing Instance TrueAction.
Local Existing Instance UnitAmbientAction.

Example ambient_still_stored
  : vertex_ambient FalsePresentation = CodiscreteCat@{Set Set Set Set} bool
  := eq_refl.

Example false_action_still_stored
  : FalsePresentation tt = false
  := eq_refl.

Example true_action_still_stored
  : TruePresentation tt = true
  := eq_refl.

Fail Definition choices_not_identified
  : FalsePresentation tt = TruePresentation tt
  := eq_refl.

End CompetingAction.

(** Finite-product presentation maps use exactly the existing selections. *)

Example product_labels_kept
  : VtxPresentationToSetC
      (VtxPresentationProduct FalsePresentation TruePresentation) =
      (UnitS@{Set Set} ×S UnitS@{Set Set})
  := eq_refl.

Example product_action_computes
  : VtxPresentationProduct FalsePresentation TruePresentation (tt, tt) =
      (false, true)
  := eq_refl.

Example terminal_action_computes
  : VtxPresentationTerminal@{Set Set Set Set Set Set Set Set} tt = tt
  := eq_refl.

Fail Definition unchosen_product
  : HasProduct VtxPresentationCat@{Set Set Set Set Set Set Set Set
      _ _ _ _ _ _ _ _ _ _}
  := ltac:(typeclasses eauto).

Fail Definition unchosen_terminal
  : HasTerminal VtxPresentationCat@{Set Set Set Set Set Set Set Set
      _ _ _ _ _ _ _ _ _ _}
  := ltac:(typeclasses eauto).

Fail Check Cats.Instance.Set.Vertex.Category.vertex_labels.
Fail Check Cats.Instance.Set.Vertex.Category.Build_VtxPresentation.

(** Native label and ambient hom equality sizes can occur in either order. *)

Section StrictSizes.
Universes e h o l.
Constraint e < h, h < o, o < l.
Context (X : SetC@{o e}) (Y : SetC@{e o})
    (H : HasVtxAction@{o e o h e l h e} X)
    (K : HasVtxAction@{e o e h o l o o} Y).

Definition lower_equality_presentation
  : VtxPresentation@{o e o h e l h e}
  := MakeVtxPresentation X H.

Definition higher_equality_presentation
  : VtxPresentation@{e o e h o l o o}
  := MakeVtxPresentation Y K.

Example lower_component_recovered
  : hasVtxAction lower_equality_presentation = H
  := eq_refl.

Example higher_component_recovered
  : hasVtxAction higher_equality_presentation = K
  := eq_refl.

End StrictSizes.
