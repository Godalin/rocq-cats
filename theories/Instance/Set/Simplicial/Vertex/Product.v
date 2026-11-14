From Cats Require Export
  Instance.Set.Vertex.Product
  Instance.Set.Simplicial.Vertex.Functor.
From Cats Require Import
  Cat.Core
  Cat.Functor.Product
  Cat.Product.Core
  Cat.Natural
  Instance.Set.Product.

Local Open Scope nat_scope.
Local Existing Instance SetCat_HasProduct.

(** * The Vertex Nerve Preserves Products

    Split and pair labelled diagrams using the general correspondence,
    then include the two native equalities at common value sizes. The
    comparison is natural in simplex operators and presentation maps. *)

(** * 顶点 nerve 保持积

    使用通用对应拆分及配对带标签图式，再将两个原生相等嵌入共同值大小。
    比较对单纯算子及呈现映射均自然。 *)

(** A diagram in a product consists of two diagrams with the same
    shape, one in each factor. The comparison c below is
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.VertexNerveProductN}
    {%[VertexNerveProductN]%}%. Each triangle commutes: projecting the pair after
    splitting is the same as first projecting the original product diagram.
    The equations %\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.vertex nerve product xCExB21}
    {%[vertex_nerve_product_β1]%}% and %\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.vertex nerve product xCExB22}
    {%[vertex_nerve_product_β2]%}%
    state these two facts degree by degree.

    Pairing the two diagrams reverses c, giving %\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.vertex nerve product iso}
    {%[vertex_nerve_product_iso]%}%.
    Thus preservation of products means a natural isomorphism with the
    pointwise product, with its projections respected. The notation
    $N_{\mathrm v}(T\times U)$ in the picture abbreviates the nerve of
    [VertexProductObjF T U]. *)

(** 积中的图式由两个同形状的图式组成，每个因子中各一个。下图的比较 c 是
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.VertexNerveProductN}
    {%[VertexNerveProductN]%}%。两个三角形都交换：拆分后投影到一个分量，等于先
    投影原来的积图式。%\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.vertex nerve product xCExB21}
    {%[vertex_nerve_product_β1]%}% 与
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.vertex nerve product xCExB22}
    {%[vertex_nerve_product_β2]%}% 逐维给出这两条方程。

    将两个图式配对就是 c 的逆，得到 %\coqref{Cats.Instance.Set.Simplicial.Vertex.Product.vertex nerve product iso}
    {%[vertex_nerve_product_iso]%}%。因此，保持
    积的意思是与逐点积自然同构，并与投影相容。图中的 $N_{\mathrm v}(T\times U)$ 简写
    [VertexProductObjF T U] 的 nerve。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
& N_{\mathrm v}(T\times U)
  \arrow[dl,"{N_{\mathrm v}(\pi_1)}"'] \arrow[d,"{c}"]
  \arrow[dr,"{N_{\mathrm v}(\pi_2)}"] & \\
N_{\mathrm v}(T) &
N_{\mathrm v}(T)\times N_{\mathrm v}(U)
  \arrow[l,"{\pi_1}"] \arrow[r,"{\pi_2}"'] & N_{\mathrm v}(U)
\end{tikzcd}
\end{center}%
*)

Section Product.
Universes u p.
Context {X : SetC} {Y : SetC} {C : Cat} {D : Cat}
    (T : Fct (EqGpd X) C) (U : Fct (EqGpd Y) D).

(** The target is the ordinary pointwise setoid product of the two nerves.
    Chosen setoid products are supplied explicitly. *)

(** 目标为两个 nerve 的通常逐点广集积；选定广集积显式提供。 *)

Definition VertexNerveProduct
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := @PointwiseProductF _ _ SetCat_HasProduct (Nᵥ(T)) (Nᵥ(U)).

(** Projection of a simplex keeps both lifted diagrams separately. *)

(** 单形投影分别保留两个提升后的图式。 *)

Program Definition VertexNerveProductN
  : (Nᵥ(VertexProductObjF T U) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ VertexNerveProduct
  :=
  {|nt n :=
      {|func x :=
          (⟨fst (vertex_diagram_product_split_resp T U [Ord n] (lower x))⟩ᵥ,
           ⟨snd (vertex_diagram_product_split_resp T U [Ord n] (lower x))⟩ᵥ)
      |}
  |}.
Next Obligation.
  intros [F] [G] [H].
  destruct (@func_proper _ _ (vertex_diagram_product_split_resp T U [Ord n])
    F G H) as [H1 H2].
  split.
  - exact {|lower := H1
           |}.
  - exact {|lower := H2
           |}.
Defined.
Next Obligation.
  intros [F]. cbn. split.
  - refine {|lower := _
            |}.
    exists (λ i, reflexivity (fst (F (f i)) : X)). intros i j a.
    rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
  - refine {|lower := _
            |}.
    exists (λ i, reflexivity (snd (F (f i)) : Y)). intros i j a.
    rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Pair two lifted simplices with the native transparent diagram pairing. *)

(** 使用原生透明图式配对，将两个提升后的单形配对。 *)

Program Definition VertexNerveProductInvN
  : VertexNerveProduct ⇒
      (Nᵥ(VertexProductObjF T U) :
        Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  :=
  {|nt n :=
      {|func xy := ⟨vertex_diagram_product_pair_resp T U [Ord n]
          (lower (fst xy), lower (snd xy))⟩ᵥ
      |}
  |}.
Next Obligation.
  intros [[F] [G]] [[F'] [G']] [[H] [K]]. refine {|lower := _
                                               |}.
  exact (@func_proper _ _ (vertex_diagram_product_pair_resp T U [Ord n])
    (F, G) (F', G') (H, K)).
Defined.
Next Obligation.
  intros [[F] [G]]. cbn.
  refine {|lower := _
           |}.
  exists (λ i, (reflexivity (F (f i) : X), reflexivity (G (f i) : Y))).
  intros i j a. split.
  - change (T⟦reflexivity (F (f j) : X)⟧Ob ∘ fmap F (fmap f a) ≈
      fmap F (fmap f a) ∘ T⟦reflexivity (F (f i) : X)⟧Ob).
    rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
  - change (U⟦reflexivity (G (f j) : Y)⟧Ob ∘ fmap G (fmap f a) ≈
      fmap G (fmap f a) ∘ U⟦reflexivity (G (f i) : Y)⟧Ob).
    rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** The comparison and its explicit inverse give a natural isomorphism. *)

(** 比较及其显式逆给出自然同构。 *)

Definition vertex_nerve_product_iso
  : (Nᵥ(VertexProductObjF T U) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N VertexNerveProduct.
Proof.
  exists VertexNerveProductN. intros n. exists (VertexNerveProductInvN n).
  split.
  - intros [F].
    exact {|lower := fst (vertex_diagram_product_iso T U [Ord n]).2.2 F
           |}.
  - intros [[F] [G]].
    destruct (snd (vertex_diagram_product_iso T U [Ord n]).2.2 (F, G))
      as [H K]. split.
    + exact {|lower := H
             |}.
    + exact {|lower := K
             |}.
Defined.

(** The first comparison projection is the nerve of the first projection. *)

(** 比较的第一投影为第一投影的 nerve。 *)

Lemma vertex_nerve_product_β1 (n : nat)
    (x : (Nᵥ(VertexProductObjF T U) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : fst (VertexNerveProductN n x) ≈S VertexNerveN (VertexFstF T U) n x.
Proof. reflexivity. Defined.

(** The second projection has the corresponding equation. *)

(** 第二投影具有相应方程。 *)

Lemma vertex_nerve_product_β2 (n : nat)
    (x : (Nᵥ(VertexProductObjF T U) :
      Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : snd (VertexNerveProductN n x) ≈S VertexNerveN (VertexSndF T U) n x.
Proof. reflexivity. Defined.

End Product.

(** The comparison is natural in both presentation variables. *)

(** 比较在两个呈现变量中均自然。 *)

Lemma vertex_nerve_product_natural@{u p +}
    {X : SetC} {Y : SetC} {X' : SetC} {Y' : SetC}
    {C : Cat} {D : Cat} {C' : Cat} {D' : Cat}
    {T : Fct (EqGpd X) C} {U : Fct (EqGpd Y) D}
    {T' : Fct (EqGpd X') C'} {U' : Fct (EqGpd Y') D'}
    (F : T →ᵥ T') (G : U →ᵥ U')
  : (VertexNerveProductN T' U' ∘Nv VertexNerveN (VertexProductF F G) :
      (Nᵥ(VertexProductObjF T U) :
        Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ _) ≈N
      (@PointwiseProductN _ _ SetCat_HasProduct _ _ _ _
        (VertexNerveN F) (VertexNerveN G) ∘Nv VertexNerveProductN T U).
Proof.
  intros n [P]. cbn. split.
  - refine {|lower := _
            |}.
    exists (λ i, reflexivity (F (fst (P i)) : X')). intros i j a.
    rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
  - refine {|lower := _
            |}.
    exists (λ i, reflexivity (G (snd (P i)) : Y')). intros i j a.
    rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.
