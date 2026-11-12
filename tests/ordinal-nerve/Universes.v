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

(** * 序数比较的独立值大小

    原生有限序数为小数据；其提升后的顶点 nerve 与标准单形支持两种严格的
    值载体／相等大小次序。 *)

Section LowEquality.
Universes p u.
Constraint p < u.

Definition low_equality_ordinal_iso (n : nat)
  : (Nᵥ(OrdinalObjectsF n) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N Δ[n]
  := ordinal_vertex_nerve_iso n.

Definition low_equality_forward (n : nat)
  : (Nᵥ(OrdinalObjectsF n) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[n]
  := OrdinalVertexNerveN n.

Definition low_equality_naturality {m n : nat} (θ : (@Hom Δ) m n)
  : (OrdinalVertexNerveN n ∘Nv VertexNerveN (OrdinalVertexMapF θ) :
      (Nᵥ(OrdinalObjectsF m) :
        Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[n]) ≈N
      (fmap StandardSimplexF θ ∘Nv OrdinalVertexNerveN m)
  := ordinal_vertex_nerve_natural θ.

End LowEquality.

Section HighEquality.
Universes u p.
Constraint u < p.

Definition high_equality_ordinal_iso (n : nat)
  : (Nᵥ(OrdinalObjectsF n) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N Δ[n]
  := ordinal_vertex_nerve_iso n.

Definition high_equality_inverse (n : nat)
  : (Δ[n] : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      Nᵥ(OrdinalObjectsF n)
  := StandardVertexNerveN n.

Definition high_equality_interval_endpoint (b : bool)
  : (OrdinalVertexNerveN 1 ∘Nv
      VertexNerveN (OrdinalVertexPointF 1 (simplex_interval_position b)) :
        (Nᵥ(VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set}) :
          Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[1]) ≈N
      (SimplicialIntervalPointN b ∘Nv VertexNerveTerminalN)
  := ordinal_vertex_interval_endpoint b.

End HighEquality.
