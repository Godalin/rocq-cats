From Cats Require Import
  Instance.Set.Simplicial.Vertex.Category
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Independent Sizes for the Bundled Nerve Functor

    Compare carrier and equality sizes in both strict orders. Stored action
    laws may have larger auxiliary universes than the bundle's bound; the
    constructor checks those laws pointwise without resizing their data. *)

Section Levels.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.

(** Value equality strictly below the carrier, with native hom equality
    also below its native arrow carrier. *)

Definition low_eq_nerve_fct
  : Fct
      VtxPresentationCat@{o e o h e l h e _ _ _ _ _ _ _ _ _ _}
      (FctCat (Δ^op) SetCat@{u o _ _ _ _ _})
  := VtxNerveF.

(** The same source supports equality strictly above the value carrier. *)

Definition high_eq_nerve_fct
  : Fct
      VtxPresentationCat@{o e o h e l h e _ _ _ _ _ _ _ _ _ _}
      (FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
  := VtxNerveF.

(** Reverse both native carrier/equality profiles. *)

Definition reverse_native_nerve_fct
  : Fct
      VtxPresentationCat@{e o e h o l o o _ _ _ _ _ _ _ _ _ _}
      (FctCat (Δ^op) SetCat@{u o _ _ _ _ _})
  := VtxNerveF.

(** Full faithfulness retains all of these independent sizes. *)

Definition low_eq_fully_faithful
  : is_fully_faithful low_eq_nerve_fct
  := vertex_nerve_fully_faithful.

Definition high_eq_fully_faithful
  : is_fully_faithful high_eq_nerve_fct
  := vertex_nerve_fully_faithful.

Definition reverse_native_fully_faithful
  : is_fully_faithful reverse_native_nerve_fct
  := vertex_nerve_fully_faithful.

(** Repack action laws from strictly larger auxiliary bounds, including
    the equality-groupoid law bound, into the chosen presentation bound. *)

Context (X : SetC@{o e}) (C : Cat@{o h e l l})
    (T : Fct@{o e Set u u p o h e l} (EqGpd@{o e u} X) C).

Definition repacked_large_action_laws
  : VtxPresentation@{o e o h e l h e}
  := VtxPresentationOf T.

End Levels.
