From Cats Require Export
  Instance.Set.Vertex.Ordinal
  Instance.Set.Simplicial.Vertex.Functor
  Instance.Set.Simplicial.Standard.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Simplicial.Homotopy.Core
  Instance.Set.Simplicial.Vertex.Terminal.

Local Open Scope nat_scope.

(** * Standard Simplices as Vertex Nerves

    The finite ordinal's specified object equality is equality of positions.
    Hence its vertex nerve agrees with the standard simplex, whose diagram
    equality is natural isomorphism. The comparison is explicit and natural
    in every simplex operator, retaining independent value sizes. *)

(** * 标准单形作为顶点 nerve

    有限序数的指定对象相等是位置相等，故其顶点 nerve 与标准单形相容；
    后者的图式相等为自然同构。显式比较对每个单纯算子自然，保留独立值大小。 *)

(** Forget the induced-category wrapper degreewise. *)

(** 逐维忘却诱导范畴包装。 *)

Program Definition OrdinalVertexNerveN@{u p +} (n : nat)
  : (Nᵥ(OrdinalObjectsF n) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[n]
  :=
  {|nt m := (vertex_ordinal_diagram_resp m n)^↑S
  |}.
Next Obligation.
  intros [P]. refine {|lower := _
                      |}.
  apply (snd (simplex_eq_iff _ _)). intros i. reflexivity.
Defined.

(** Reintroduce the finite positions as labels. *)

(** 重新将有限位置作为标签。 *)

Program Definition StandardVertexNerveN@{u p +} (n : nat)
  : (Δ[n] : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      Nᵥ(OrdinalObjectsF n)
  :=
  {|nt m := (vertex_ordinal_diagram_inv_resp m n)^↑S
  |}.
Next Obligation.
  intros [P]. refine {|lower := _
                      |}.
  apply (snd (vertex_ordinal_diagram_eq_iff n _ _)).
  intros i. reflexivity.
Defined.

(** Both maps form a natural isomorphism, comparing diagrams in their
    specified equality rather than identifying functor-law fields. *)

(** 双向映射组成自然同构，在指定相等中比较图式，而不识别函子定律字段。 *)

Definition ordinal_vertex_nerve_iso@{u p +} (n : nat)
  : (Nᵥ(OrdinalObjectsF n) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N Δ[n].
Proof.
  exists (OrdinalVertexNerveN n). intros m.
  exists (StandardVertexNerveN n m). split; intros [P];
    refine {|lower := _
            |}.
  - apply (snd (vertex_ordinal_diagram_eq_iff n _ _)).
    intros i. reflexivity.
  - apply (snd (simplex_eq_iff _ _)). intros i. reflexivity.
Defined.

(** The comparison also commutes with changing the represented ordinal,
    including every face and degeneracy map. *)

(** 比较也与改变所表序数相交换，特别包含每个面及退化映射。 *)

Lemma ordinal_vertex_nerve_natural@{u p +} {m n : nat}
    (θ : (@Hom Δ) m n)
  : (OrdinalVertexNerveN n ∘Nv VertexNerveN (OrdinalVertexMapF θ) :
      (Nᵥ(OrdinalObjectsF m) :
        Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[n]) ≈N
      (fmap StandardSimplexF θ ∘Nv OrdinalVertexNerveN m).
Proof.
  intros k [P]. refine {|lower := _
                        |}.
  apply (snd (simplex_eq_iff _ _)). intros i. reflexivity.
Defined.

(** For the interval ordinal the two presentation points are exactly the
    already chosen simplicial endpoints after the terminal comparison. *)

(** 对区间序数，在终比较之后，两个呈现点恰对应已有的单纯端点。 *)

Lemma ordinal_vertex_interval_endpoint@{u p +} (b : bool)
  : (OrdinalVertexNerveN 1 ∘Nv
      VertexNerveN (OrdinalVertexPointF 1 (simplex_interval_position b)) :
        (Nᵥ(VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set}) :
          Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Δ[1]) ≈N
      (SimplicialIntervalPointN b ∘Nv VertexNerveTerminalN).
Proof.
  intros n [P]. refine {|lower := _
                        |}.
  apply (snd (simplex_eq_iff _ _)). intros i. reflexivity.
Defined.
