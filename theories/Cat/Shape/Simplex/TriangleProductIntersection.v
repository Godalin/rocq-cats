From Cats Require Export
  Cat.Shape.Simplex.TriangleProduct.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Six Shared Facets of the Triangle Product

    Swapping one adjacent vertical/horizontal step gives a neighboring
    staircase. The six pairs (0,1), (1,2), (1,3), (2,4), (3,4), (4,5)
    omit positions 2, 3, 1, 1, 3, 2 respectively. Both coordinate
    equations hold on each actual shared facet. Conversely, an arbitrary
    common simplex of a listed pair factors through that facet, even
    in a source degree larger than four.

    This proves these intersections, not a shelling or attachment order.
    In particular no horn extension or equality of chosen fillers occurs. *)

(** * 三角积的六个共享面

    交换相邻的一次竖直步与水平步得到相邻阶梯。六对 (0,1)、(1,2)、(1,3)、
    (2,4)、(3,4)、(4,5) 分别省略位置 2、3、1、1、3、2。每个实际共享面
    都满足两个坐标方程。反之，列出的每对阶梯的任意共同单形都经过该面，
    即使来源维数大于四也成立。

    此处证明这些交叠，尚不给出剥壳或附着次序，不使用 horn 延拓或填充选择相等。 *)

(** Edges below indicate common facets. Labels are the coface omitted
    positions, rather than arrows between whole staircases. *)

(** 下图边表示共享面，标号为余面省略位置，不表示整个阶梯之间的映射。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
& & {0} \arrow[d,no head,"{\delta_2}"] & & \\
& & {1} \arrow[dl,no head,"{\delta_1}"']
        \arrow[dr,no head,"{\delta_3}"] & & \\
& {3} \arrow[dr,no head,"{\delta_3}"'] & &
  {2} \arrow[dl,no head,"{\delta_1}"] & \\
& & {4} \arrow[d,no head,"{\delta_2}"] & & \\
& & {5} & &
\end{tikzcd}
\end{center}%
*)

(** The table stores the two staircase indices and their common omitted
    position. Indices name the pivot pairs in
    %\coqref{Cats.Cat.Shape.Simplex.TriangleProduct.simplex_triangle_product_pivots}
    {%[simplex_triangle_product_pivots]%}%. *)

(** 表中保存两个阶梯索引及共享省略位置；索引对应
    %\coqref{Cats.Cat.Shape.Simplex.TriangleProduct.simplex_triangle_product_pivots}
    {%[simplex_triangle_product_pivots]%}% 的枢轴对。 *)

Definition simplex_triangle_product_adjacency (e : Ordinal 5)
  : (Ordinal 5 * Ordinal 5) * Ordinal 4
  := match e with
  | inl _ => ((fin_first, fin_first⁺↑↑↑↑), fin_first⁺⁺↑↑)
  | inr (inl _) => ((fin_first⁺↑↑↑↑, fin_first⁺⁺↑↑↑), fin_first⁺⁺⁺↑)
  | inr (inr (inl _)) =>
      ((fin_first⁺↑↑↑↑, fin_first⁺⁺⁺↑↑), fin_first⁺↑↑↑)
  | inr (inr (inr (inl _))) =>
      ((fin_first⁺⁺↑↑↑, fin_first⁺⁺⁺⁺↑), fin_first⁺↑↑↑)
  | inr (inr (inr (inr (inl _)))) =>
      ((fin_first⁺⁺⁺↑↑, fin_first⁺⁺⁺⁺↑), fin_first⁺⁺⁺↑)
  | inr (inr (inr (inr (inr _)))) =>
      ((fin_first⁺⁺⁺⁺↑, fin_first⁺⁺⁺⁺⁺), fin_first⁺⁺↑↑)
  end.

(** ** Both Coordinates and the Missing Position

    Fix one edge of the finite adjacency graph. Its two spatial and
    temporal projections agree after the indicated coface, whereas
    their spatial values differ at the omitted position itself. *)

(** ** 两个坐标及省略位置

    固定有限相邻图的一条边。两侧空间与时间投影经过指定余面后一致，而空间
    坐标在省略位置本身取不同值。 *)

Section SharedFacet.
Context (e : Ordinal 5).

Let i
  : Ordinal 5
  := fst (fst (simplex_triangle_product_adjacency e)).

Let j
  : Ordinal 5
  := snd (fst (simplex_triangle_product_adjacency e)).

Let r
  : Ordinal 4
  := snd (simplex_triangle_product_adjacency e).

(** The spatial coordinates agree on the shared three-face. *)

(** 空间坐标在共享三面上一致。 *)

Lemma simplex_triangle_product_adjacent_space
  : SimplexTriangleProductSpaceF i ∘ δ[3; r] ≈
      SimplexTriangleProductSpaceF j ∘ δ[3; r].
Proof.
  apply (snd (simplex_eq_iff _ _)). intros z.
  destruct e as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]];
    destruct z as [[] | [[] | [[] | [[] | []]]]]; reflexivity.
Defined.

(** The temporal coordinates agree on the same three-face. *)

(** 时间坐标在同一三面上一致。 *)

Lemma simplex_triangle_product_adjacent_time
  : SimplexTriangleProductTimeF i ∘ δ[3; r] ≈
      SimplexTriangleProductTimeF j ∘ δ[3; r].
Proof.
  apply (snd (simplex_eq_iff _ _)). intros z.
  destruct e as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]];
    destruct z as [[] | [[] | [[] | [[] | []]]]]; reflexivity.
Defined.

(** The excluded position cannot belong to the intersection. *)

(** 被省略位置不能属于交叠。 *)

Lemma simplex_triangle_product_adjacent_separated
  : ¬ SimplexTriangleProductSpaceF i r = SimplexTriangleProductSpaceF j r.
Proof.
  destruct e as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]];
    discriminate.
Defined.

(** Two actual coordinate equations construct a shared-face mediator.
    The given factors need not be the same operator record. The mediator
    uses [CofacePreimageF] and retains both reconstruction equations. *)

(** 两个实际坐标方程构造共享面中介；给定因子不必是同一算子记录。中介复用
    [CofacePreimageF]，并保留两个重构方程。 *)

Definition SimplexTriangleProductAdjacentFactor {n : nat}
    (f g : (@Hom Δ) n 4)
    (E : SimplexTriangleProductSpaceF i ∘ f ≈
      SimplexTriangleProductSpaceF j ∘ g)
    (F : SimplexTriangleProductTimeF i ∘ f ≈
      SimplexTriangleProductTimeF j ∘ g)
  : ∃ h : (@Hom Δ) n 3,
      (δ[3; r] ∘ h ≈ f) ∧ (δ[3; r] ∘ h ≈ g).
Proof.
  pose proof (simplex_triangle_product_factors_eq i j f g E F) as G.
  assert (H : ∀ z, ¬ f z = r).
  { intros z V. apply simplex_triangle_product_adjacent_separated.
    pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
    pose proof (fst (simplex_eq_iff _ _) G z) as Gz.
    change (SimplexTriangleProductSpaceF i (f z) =
      SimplexTriangleProductSpaceF j (g z)) in Ez.
    change (f z = g z) in Gz.
    rewrite <- Gz, V in Ez. exact Ez. }
  exists (CofacePreimageF r f H). split.
  - apply coface_preimage_β.
  - transitivity f; [apply coface_preimage_β | exact G].
Defined.

End SharedFacet.
