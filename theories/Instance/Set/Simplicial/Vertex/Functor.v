From Cats Require Export
  Instance.Set.Vertex.Functor
  Instance.Set.Simplicial.Vertex.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Yoneda.

(** * The Vertex Nerve on Transport-Preserving Functors

    Postcomposition acts degreewise on labelled diagrams. Preservation of
    transport makes this action respectful; associativity gives naturality
    with respect to every simplex operator. *)

(** * 顶点 nerve 在保运输函子上的作用

    后复合逐维作用于带标签图式。保持运输保证此作用保相等；结合律给出它对每个
    单纯算子的自然性。 *)

(** Start with a labelled chain P of length n. A functor F sends
    every vertex and arrow of P to its image. A shape operator θ selects,
    repeats or composes parts of that chain by precomposition. The square
    below says that changing the chain's shape and applying F can be done
    in either order. It is %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict natural}
    {%[simplex_restrict_natural]%}% for [VertexNerveN F].

    For a triangle, selecting its middle face gives the familiar equation
    that F preserves composition. For a repeated vertex, it gives identity
    preservation. Transport preservation additionally ensures that equal
    labelled chains have equal image chains. *)

(** 从长度为 n 的带标签箭头链 P 出发，函子 F 把每个顶点和每条箭头送到其像。
    形状算子 θ 则通过预合成选取、重复或复合链的一部分。下图说明，改变链的
    形状与应用 F 可以按任一次序进行。这就是 [VertexNerveN F] 所满足的
    %\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict natural}
    {%[simplex_restrict_natural]%}%。

    对三角形选取中间面，得到的就是 F 保持复合的方程；对重复顶点，得到的是
    保持恒等。保持运输还保证相等的带标签链具有相等的像链。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
N_{\mathrm v}(T)_n \arrow[r,"{N_{\mathrm v}(F)_n}"]
  \arrow[d,"{[\theta]}"'] &
N_{\mathrm v}(U)_n \arrow[d,"{[\theta]}"] \\
N_{\mathrm v}(T)_m \arrow[r,"{N_{\mathrm v}(F)_m}"'] & N_{\mathrm v}(U)_m
\end{tikzcd}
\end{center}%
*)

(** A transport-preserving functor induces a simplicial map. Both nerves
    use common value sizes; their native object and hom sizes stay separate. *)

(** 保运输函子诱导单纯映射。两个 nerve 使用共同值大小，其原生对象及 Hom 大小
    仍保持独立。 *)

Program Definition VertexNerveN@{u p +} {X Y : SetC} {C D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D} (F : T →ᵥ U)
  : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U)
  :=
  {|nt n := (vertex_diagram_postcomp_resp (J := [Ord n]) F)^↑S
  |}.
Next Obligation.
  intros [P]. refine {|lower := _
                     |}.
  exists (λ i, reflexivity (F (P (f i)) : Y)). intros i j a.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Prescribed natural-isomorphism comparisons induce equal simplicial
    maps, in pointwise specified simplex equality. *)

(** 指定自然同构比较诱导相等的单纯映射，其相等为逐点指定单形相等。 *)

Global Instance vertex_nerve_proper@{u p +}
    {X Y : SetC} {C D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D}
  : Proper (VertexFunctorEq ==>
      @NatEq _ _
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (Nᵥ(U)))
      (@VertexNerveN X Y C D T U).
Proof.
  intros F G H n [P]. refine {|lower := _
                            |}.
  exact (vertex_diagram_postcomp_proper F G H P).
Defined.

(** The forward map is respectful between the native hom-setoids.
    The inverse and both round-trip laws are defined in [Reconstruction]. *)

(** 前向映射保持原生态射广集的相等。逆及两侧往返律在 [Reconstruction] 中定义。 *)

Program Definition vertex_nerve_resp@{u p +} {X Y : SetC} {C D : Cat}
    (T : Functor (EqGpd X) C) (U : Functor (EqGpd Y) D)
  : VertexFunctorS T U →r Nat_SetS
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (Nᵥ(U))
  :=
  {|func := VertexNerveN
  |}.

(** Identity functors induce identity simplicial maps. *)

(** 恒等函子诱导恒等单纯映射。 *)

Lemma vertex_nerve_id@{u p +} {X : SetC} {C : Cat}
    (T : Functor (EqGpd X) C)
  : (VertexNerveN (VertexIdF T) :
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ _) ≈N idN.
Proof.
  intros n [P]. refine {|lower := _
                       |}.
  exists (λ i, reflexivity (P i : X)). intros i j f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Composition of transport-preserving functors induces vertical
    composition of simplicial maps, with no equality of functor records. *)

(** 保运输函子的复合诱导单纯映射的垂直复合，不要求函子记录相等。 *)

Lemma vertex_nerve_comp@{u p +} {X Y Z : SetC} {C D E : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D}
    {V : Functor (EqGpd Z) E} (G : U →ᵥ V) (F : T →ᵥ U)
  : (VertexNerveN (G ∘Fᵥ F) :
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(V)) ≈N
      (VertexNerveN G ∘Nv VertexNerveN F).
Proof.
  intros n [P]. refine {|lower := _
                       |}.
  exists (λ i, reflexivity (G (F (P i)) : Z)). intros i j f.
  rewrite !vertex_transport_id, comp_id_l, comp_id_r. reflexivity.
Defined.
