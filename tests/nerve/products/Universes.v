From Cats Require Import
  Instance.Set.Simplicial.Vertex.Product
  Instance.Set.Simplicial.Vertex.Terminal
  Cat.Core
  Cat.Functor.Product
  Cat.Natural
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Product.

(** * Independent Sizes for Vertex Nerve Products

    Exchange the native object and hom equality profiles of the factors.
    Common value equality is tested strictly below and above its carrier,
    without assuming that either selected category is a groupoid. *)

Section Products.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.
Context (X : SetC@{o e}) (Y : SetC@{e o})
    (C : Cat@{o h e l l}) (D : Cat@{e h o l l})
    (T : Fct (EqGpd X) C) (U : Fct (EqGpd Y) D).

(** Product comparison with value equality below the value carrier. *)

Definition low_eq_product_iso
  : (Nᵥ(VtxProductObjF T U) :
      Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ≅N VtxNerveProduct T U
  := vertex_nerve_product_iso T U.

(** Product comparison with value equality above the value carrier. *)

Definition high_eq_product_iso
  : (Nᵥ(VtxProductObjF T U) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N VtxNerveProduct T U
  := vertex_nerve_product_iso T U.

(** Exchange the two native size profiles. *)

Definition reverse_product_iso
  : (Nᵥ(VtxProductObjF U T) :
      Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ≅N VtxNerveProduct U T
  := vertex_nerve_product_iso U T.

(** The native correspondence also admits a larger arbitrary probe. *)

Definition native_diagram_product_iso (J : Cat@{e h o l l})
  : VtxDiagramS (VtxProductObjF T U) J ≅[SetCat]
      (VtxDiagramS T J ×S VtxDiagramS U J)
  := vertex_diagram_product_iso T U J.

(** Terminal diagram comparison must not force the probe to be small. *)

Definition native_diagram_terminal_iso (J : Cat@{e h o l l})
  : VtxDiagramS VtxTerminalObjF J ≅[SetCat] UnitS@{l o}
  := vertex_diagram_terminal_iso J.

(** Naturality exchanges factors with different native size profiles. *)

Definition exchanged_product_naturality (F : T →ᵥ U) (G : U →ᵥ T)
  : (VtxNerveProductN U T ∘Nv VtxNerveN (VtxProductF F G) :
      (Nᵥ(VtxProductObjF T U) :
        Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ _) ≈N
      (@PointwiseProductN _ _ SetCat_HasProduct _ _ _ _
        (VtxNerveN F) (VtxNerveN G) ∘Nv VtxNerveProductN T U)
  := vertex_nerve_product_natural F G.

End Products.

(** Terminal comparison also keeps value carrier and equality independent. *)

Section Terminal.
Universes u p.
Constraint u < p.

Definition low_eq_terminal_iso
  : (Nᵥ(VtxTerminalObjF) :
      Fct (Δ^op) SetCat@{p u _ _ _ _ _}) ≅N
      ConstF (Δ^op) UnitS@{p u}
  := vertex_nerve_terminal_iso.

Definition high_eq_terminal_iso
  : (Nᵥ(VtxTerminalObjF) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      ConstF (Δ^op) UnitS@{u p}
  := vertex_nerve_terminal_iso.

End Terminal.
