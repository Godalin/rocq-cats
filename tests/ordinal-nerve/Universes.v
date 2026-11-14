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

(** ** Equality below the Value Carrier

    Fix value sizes [p < u]. Check the ordinal comparison isomorphism,
    its forward map and naturality in the represented ordinal at these sizes. *)

(** ** 相等低于值载体

    固定值大小 [p < u]，在此配置下检查序数比较同构、前向映射及其对所表序数
    的自然性。 *)

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
  := OrdinalVertexNerveN n.

Definition low_equality_naturality {m n : nat} (θ : (@Hom Δ) m n)
  : (OrdinalVertexNerveN n ∘Nv VertexNerveN (OrdinalVertexMapF θ) :
      (Nᵥ(OrdinalObjF m) :
        Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[n]) ≈N
      (fmap StandardSimplexF θ ∘Nv OrdinalVertexNerveN m)
  := ordinal_vertex_nerve_natural θ.

End LowEquality.

(** ** Equality above the Value Carrier

    Now fix [u < p]. Check the same comparison, its inverse and the two
    interval endpoint equations without coupling the two value sizes. *)

(** ** 相等高于值载体

    现在固定 [u < p]，检查同一比较、其逆及两个区间端点方程，而不耦合两个
    值大小。 *)

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
  := StandardVertexNerveN n.

Definition high_equality_interval_endpoint (b : bool)
  : (OrdinalVertexNerveN 1 ∘Nv
      VertexNerveN (OrdinalVertexPointF 1 (simplex_interval_position b)) :
        (Nᵥ(VertexTerminalObjF@{Set Set Set Set Set Set Set Set}) :
          Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[1]) ≈N
      (SimplicialIntervalPointN b ∘Nv VertexNerveTerminalN)
  := ordinal_vertex_interval_endpoint b.

End HighEquality.
