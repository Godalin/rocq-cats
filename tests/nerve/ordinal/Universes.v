From Cats Require Import
  Instance.Set.Simplicial.Vertex.Ordinal
  Instance.Set.Simplicial.Homotopy.Core
  Instance.Set.Simplicial.Vertex.Terminal
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Independent Value Sizes for the Ordinal Comparison

    Native finite ordinals are small. Their raised vertex nerves and
    standard simplices support both strict value carrier/equality orders. *)

(** ** Equality below the Value Carrier

    Fix value sizes [p < u]. Check the ordinal comparison isomorphism,
    its forward map and naturality in the represented ordinal at these sizes. *)

Section LowEquality.
Universes p u.
Constraint p < u.

Definition low_equality_ordinal_iso (n : nat)
  : (Nᵥ(OrdinalObjF n) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N Δ[n]
  := ordinal_vertex_nerve_iso n.

Definition low_equality_forward (n : nat)
  : (Nᵥ(OrdinalObjF n) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[n]
  := OrdinalVtxNerveN n.

Definition low_equality_naturality {m n : nat} (θ : (@Hom Δ) m n)
  : (OrdinalVtxNerveN n ∘Nv VtxNerveN (OrdinalVtxMapF θ) :
      (Nᵥ(OrdinalObjF m) :
        Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[n]) ≈N
      (fmap StandardSimplexF θ ∘Nv OrdinalVtxNerveN m)
  := ordinal_vertex_nerve_natural θ.

End LowEquality.

(** ** Equality above the Value Carrier

    Now fix [u < p]. Check the same comparison, its inverse and the two
    interval endpoint equations without coupling the two value sizes. *)

Section HighEquality.
Universes u p.
Constraint u < p.

Definition high_equality_ordinal_iso (n : nat)
  : (Nᵥ(OrdinalObjF n) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N Δ[n]
  := ordinal_vertex_nerve_iso n.

Definition high_equality_inverse (n : nat)
  : (Δ[n] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      Nᵥ(OrdinalObjF n)
  := StandardVtxNerveN n.

Definition high_equality_interval_endpoint (b : bool)
  : (OrdinalVtxNerveN 1 ∘Nv
      VtxNerveN (OrdinalVtxPointF 1 (simplex_interval_position b)) :
        (Nᵥ(VtxTerminalObjF@{Set Set Set Set Set Set Set Set}) :
          Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[1]) ≈N
      (SimplicialIntervalPointN b ∘Nv VtxNerveTerminalN)
  := ordinal_vertex_interval_endpoint b.

End HighEquality.
