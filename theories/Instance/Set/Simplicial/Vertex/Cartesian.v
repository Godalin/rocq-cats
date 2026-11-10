From Cats Require Export
  Instance.Set.Vertex.FiniteProducts
  Instance.Set.Simplicial.Vertex.Category.
From Cats Require Import
  Cat.Core
  Cat.Functor.Cartesian
  Cat.Functor.FiniteProducts
  Cat.Product.Core
  Cat.Product.Transport
  Cat.Terminal
  Cat.Natural
  Instance.Set.Simplicial.Vertex.Product
  Instance.Set.Simplicial.Vertex.Terminal.

(** * The Cartesian Vertex Nerve Functor

    The existing natural comparisons transport the pointwise universal
    properties. The resulting bundle retains the original nerve functor;
    all chosen model structures require explicit enabling. *)

(** * 笛卡尔顶点 nerve 函子

    已有自然比较运输点态泛性质。所得打包保留原 nerve 函子；全部选定模型
    结构均要求显式启用。 *)

Section Cartesian.
Universes u r x e o h p l a b.

Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** The image of the chosen terminal presentation is terminal by its
    existing comparison with the constant singleton diagram. *)

(** 选定终呈现的像由已有常值单元素图式比较得到终性。 *)

Definition vertex_nerve_terminal_universal
  : is_terminal (C := Fct (Δ^op) SetCat@{u r _ _ _ _ _})
      (Nᵥ(VertexPresentationTerminal@{x e o h p l a b})).
Proof.
  pose (i := vertex_nerve_terminal_iso).
  pose (j := ((i.1; NatIso_is_iso i.1 i.2) :
    _ ≅[Fct (Δ^op) SetCat@{u r _ _ _ _ _}] _)).
  exact (terminal_iso
    (@pointwise_terminal_universal (Δ^op) _ SetCat_HasTerminal)
    (iso_symm j)).
Defined.

(** The product comparison transfers the pointwise product cone to the
    image cone; its projection equations identify the two legs. *)

(** 积比较将点态积锥转移至像锥，其投影方程识别两条锥腿。 *)

Definition vertex_nerve_product_universal
    (P Q : VertexPresentation@{x e o h p l a b})
  : is_product (C := Fct (Δ^op) SetCat@{u r _ _ _ _ _})
      (Nᵥ(P)) (Nᵥ(Q)) (Nᵥ(VertexPresentationProduct P Q))
      (VertexNerveN (VertexFstF P Q)) (VertexNerveN (VertexSndF P Q)).
Proof.
  pose (i := vertex_nerve_product_iso P Q).
  pose (j := ((i.1; NatIso_is_iso i.1 i.2) :
    _ ≅[Fct (Δ^op) SetCat@{u r _ _ _ _ _}] _)).
  refine (product_apex_iso
    (@pointwise_product_universal (Δ^op) _ SetCat_HasProduct (Nᵥ(P)) (Nᵥ(Q)))
    (iso_symm j) _ _ _ _).
  - intros n [z1 z2]. change
      (VertexNerveN (VertexFstF P Q) n (j.2.1 n (z1, z2)) ≈S z1).
    transitivity (fst (i.1 n (j.2.1 n (z1, z2)))).
    + symmetry. apply vertex_nerve_product_β1.
    + destruct (snd j.2.2 n (z1, z2)) as [H1 H2]. exact H1.
  - intros n [z1 z2]. change
      (VertexNerveN (VertexSndF P Q) n (j.2.1 n (z1, z2)) ≈S z2).
    transitivity (snd (i.1 n (j.2.1 n (z1, z2)))).
    + symmetry. apply vertex_nerve_product_β2.
    + destruct (snd j.2.2 n (z1, z2)) as [H1 H2]. exact H2.
Defined.

(** Preservation uses the general cartesian-functor property class and
    the explicitly named source terminal and product structures. *)

(** 保持性使用通用笛卡尔函子性质类，显式具名源终对象及积结构。 *)

Program Definition VertexNerveF_IsCartesianF
  : IsCartesianF
      (VertexNerveF : Functor
        VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
        (Fct (Δ^op) SetCat@{u r _ _ _ _ _}))
      VertexPresentationCat_HasTerminal VertexPresentationCat_HasProduct
  :=
  {|functor_terminal := vertex_nerve_terminal_universal
  ; functor_product := vertex_nerve_product_universal
  |}.

(** Bundle exactly the existing nerve and its preservation evidence. *)

(** 精确保留已有 nerve 及其保持性证据进行打包。 *)

Definition VertexNerveCartesianF
  : @CartesianFunctor
      VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
      (Fct (Δ^op) SetCat@{u r _ _ _ _ _})
      VertexPresentationCat_HasTerminal VertexPresentationCat_HasProduct
  := CartesianFunctorFromPreservation VertexNerveF VertexNerveF_IsCartesianF.

End Cartesian.
