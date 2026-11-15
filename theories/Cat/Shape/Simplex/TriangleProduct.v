From Cats Require Export
  Cat.Shape.Simplex.Prism.
From Cats.Set Require Import
  OrdinalMaximum.
From Cats Require Import
  Cat.Core.
From Stdlib Require Import
  Arith.PeanoNat
  Lia.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Six Staircases in a Product of Triangles

    A maximal monotone path in the 3 by 3 vertex grid has four steps.
    Its two vertical steps occur at spatial positions k and l, with
    k ≤ l. The six possibilities are (0,0), (0,1), (0,2), (1,1),
    (1,2), (2,2). Each gives an actual pair of operators [4] → [2].

    Factorization reuses the two-coordinate cylinder construction in
    %\coqref{Cats.Cat.Shape.Simplex.Prism.SimplexPrismFactor}
    {%[SimplexPrismFactor]%}%: split the second coordinate at levels
    zero and one, and insert the two time changes in that order.
    The resulting cover is shape theory. It does not yet give a horn
    attachment order or a pushout, nor extend a map into a Kan object. *)

(** * 三角积中的六条阶梯

    3 乘 3 顶点格中的极大保序路径共有四步。两次竖直步分别发生于空间位置
    k、l，且 k ≤ l；共有 (0,0)、(0,1)、(0,2)、(1,1)、(1,2)、(2,2)
    六种可能。每种给出一对实际算子 [4] → [2]。

    分解复用 %\coqref{Cats.Cat.Shape.Simplex.Prism.SimplexPrismFactor}
    {%[SimplexPrismFactor]%}% 的双坐标柱构造：在零和一处分割第二坐标，
    依次插入两次时间变化。所得覆盖属于形状理论，尚不给出 horn 附着次序、
    推出或到 Kan 对象的映射延拓。 *)

(** Every product simplex has an actual staircase factor making both
    triangles commute in the specified equality. The corresponding
    presheaf cover is proved in
    %\coqref{Cats.Instance.Set.Simplicial.TriangleProduct.simplex_triangle_product_cover}
    {%[simplex_triangle_product_cover]%}%. *)

(** 每个积单形都有实际阶梯因子，使两个三角形按指定相等交换。对应的预层
    覆盖见 %\coqref{Cats.Instance.Set.Simplicial.TriangleProduct.simplex_triangle_product_cover}
    {%[simplex_triangle_product_cover]%}%。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
& {[4]_i} \arrow[dl,"{s_i}"'] \arrow[dr,"{t_i}"] & \\
{[2]} & {[n]} \arrow[l,"a"] \arrow[u,dashed,"h"] \arrow[r,"b"'] & {[2]}
\end{tikzcd}
\end{center}%
*)

(** The index lists the ordered pivot pairs in lexicographic order. *)

(** 索引按字典序列出有序枢轴对。 *)

Definition simplex_triangle_product_pivots (i : Ordinal 5)
  : Ordinal 2 * Ordinal 2
  := match i with
  | inl _ => (fin_first, fin_first)
  | inr (inl _) => (fin_first, fin_first⁺↑)
  | inr (inr (inl _)) => (fin_first, fin_first⁺⁺)
  | inr (inr (inr (inl _))) => (fin_first⁺↑, fin_first⁺↑)
  | inr (inr (inr (inr (inl _)))) => (fin_first⁺↑, fin_first⁺⁺)
  | inr (inr (inr (inr (inr _)))) => (fin_first⁺⁺, fin_first⁺⁺)
  end.

(** Every listed pair is ordered. *)

(** 列出的每对枢轴都按序排列。 *)

Lemma simplex_triangle_product_pivots_order (i : Ordinal 5)
  : fin_rank (fst (simplex_triangle_product_pivots i)) ≤
      fin_rank (snd (simplex_triangle_product_pivots i)).
Proof.
  destruct i as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]];
    cbn; lia.
Defined.

(** Spatial projection repeats first k, then l; the second insertion
    occurs at position l+1 after the first insertion. *)

(** 空间投影先重复 k、再重复 l；第一次插入后，第二次插入位于 l+1。 *)

Definition SimplexTriangleProductSpaceF (i : Ordinal 5)
  : (@Hom Δ) 4 2
  := σ[2; fst (simplex_triangle_product_pivots i)] ∘
      σ[3; (snd (simplex_triangle_product_pivots i))⁺].

(** The second coordinate counts the two time changes. The existing
    interleaved index adds the ranks of these two interval coordinates. *)

(** 第二坐标计数两次时间变化；既有交织索引相加两个区间坐标的编号。 *)

Definition SimplexTriangleProductTimeF (i : Ordinal 5)
  : (@Hom Δ) 4 2
  := SimplexPrismIndexF
      (SimplexPrismTimeF (fst (simplex_triangle_product_pivots i)) ∘
        σ[3; (snd (simplex_triangle_product_pivots i))⁺])
      (SimplexPrismTimeF (snd (simplex_triangle_product_pivots i))⁺).

(** The two coordinates recover the position by adding their ranks.
    In particular a staircase has no repeated pair of vertices. *)

(** 两坐标编号之和恢复位置，因此同一阶梯不重复任何顶点对。 *)

Lemma simplex_triangle_product_coordinate_rank (i : Ordinal 5)
    (j : Ordinal 4)
  : fin_rank j = fin_rank (SimplexTriangleProductSpaceF i j) +
      fin_rank (SimplexTriangleProductTimeF i j).
Proof.
  destruct i as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]];
    destruct j as [[] | [[] | [[] | [[] | [[] | []]]]]]; reflexivity.
Defined.

(** Encode ordered pivots without carrying an equality of bound proofs.
    The values on unordered input are unused. *)

(** 编码有序枢轴，不携带界证明相等；无序输入的取值不被使用。 *)

Definition simplex_triangle_product_index (k l : Ordinal 2)
  : Ordinal 5
  := match k, l with
  | inl _, inl _ => fin_first
  | inl _, inr (inl _) => fin_first⁺↑↑↑↑
  | inl _, inr (inr _) => fin_first⁺⁺↑↑↑
  | inr (inl _), inl _ => fin_first⁺⁺⁺↑↑
  | inr (inl _), inr (inl _) => fin_first⁺⁺⁺↑↑
  | inr (inl _), inr (inr _) => fin_first⁺⁺⁺⁺↑
  | inr (inr _), _ => fin_first⁺⁺⁺⁺⁺
  end.

(** Decoding an ordered pair recovers both actual finite positions. *)

(** 解码有序对恢复两个实际有限位置。 *)

Lemma simplex_triangle_product_index_pivots (k l : Ordinal 2)
    (H : fin_rank k ≤ fin_rank l)
  : simplex_triangle_product_pivots (simplex_triangle_product_index k l) =
      (k, l).
Proof.
  destruct k as [[] | [[] | [[] | []]]],
    l as [[] | [[] | [[] | []]]]; cbn in *; try lia; reflexivity.
Defined.

(** ** Factoring Arbitrary Product Simplices

    Fix two monotone coordinates with any common source dimension.
    The two interval thresholds are codegeneracies of the second
    coordinate. Their finite maxima compute the ordered pivots; no
    search for a factorization witness is assumed. *)

(** ** 分解任意积单形

    固定任意同源维数的两个保序坐标。第二坐标的两个余退化给出区间阈值，
    它们的有限最大值计算有序枢轴，不预设分解见证的搜索结果。 *)

Section ProductFactor.
Context {n : nat} (a b : (@Hom Δ) n 2).

Let t0
  : (@Hom Δ) n 1
  := σ[1; fin_first⁺] ∘ b.

Let t1
  : (@Hom Δ) n 1
  := σ[1; fin_first] ∘ b.

Let k
  : Ordinal 2
  := simplex_prism_pivot a t0.

Let l
  : Ordinal 2
  := simplex_prism_pivot a t1.

(** The zero-level maximum is bounded by the one-level maximum. *)

(** 零层最大值不超过一层最大值。 *)

Lemma simplex_triangle_product_pivot_order
  : fin_rank k ≤ fin_rank l.
Proof.
  unfold k, simplex_prism_pivot.
  apply finite_ordinal_max_bound. intros j.
  pose proof (finite_ordinal_max_upper (m := 2)
    (λ i : Ordinal n, if Nat.eqb (fin_rank (t1 i)) 0
      then (a i : Ordinal 2) else fin_first) j) as H.
  change (fin_rank (if Nat.eqb (fin_rank (t0 j)) 0
    then a j else fin_first) ≤ fin_rank l).
  change (fin_rank (if Nat.eqb (fin_rank (t1 j)) 0
    then a j else fin_first) ≤ fin_rank l) in H.
  unfold t0, t1 in *.
  change (fin_rank (if Nat.eqb
      (fin_rank (@fin_merge 1 (fin_first⁺ : Ordinal 1) (b j))) 0
    then a j else fin_first) ≤ fin_rank l).
  change (fin_rank (if Nat.eqb
      (fin_rank (@fin_merge 1 (fin_first : Ordinal 1) (b j))) 0
    then a j else fin_first) ≤ fin_rank l) in H.
  destruct (b j) as [[] | [[] | [[] | []]]]; cbn in *; lia.
Defined.

(** Every pair factors through one of the six actual staircases.
    Two applications of the existing prism factor equations supply
    the monotone factor and retain both coordinate equations. *)

(** 每对坐标经过六条实际阶梯之一分解。两次应用既有棱柱分解方程，给出
    保序因子并保留两个坐标方程。 *)

Definition SimplexTriangleProductFactor
  : ∃ i : Ordinal 5, ∃ h : (@Hom Δ) n 4,
      (SimplexTriangleProductSpaceF i ∘ h ≈ a) ∧
      (SimplexTriangleProductTimeF i ∘ h ≈ b).
Proof.
  pose (c := SimplexPrismIndexF a t0).
  pose (h := SimplexPrismIndexF c t1).
  assert (H0 : ∀ j, fin_rank (t1 j) = 0 → fin_rank (c j) ≤ fin_rank l⁺).
  { intros j E.
    change (fin_rank (@simplex_prism_position 2 (a j) (t0 j)) ≤ fin_rank l⁺).
    rewrite simplex_prism_position_rank, ordinal_next_rank.
    pose proof (simplex_prism_pivot_lower a t1 j E).
    assert (T : fin_rank (t0 j) ≤ 1).
    { destruct (t0 j) as [[] | [[] | []]]; cbn; lia. }
    unfold l. lia. }
  assert (H1 : ∀ j, fin_rank (t1 j) = 1 → fin_rank l⁺ ≤ fin_rank (c j)).
  { intros j E.
    change (fin_rank l⁺ ≤ fin_rank (@simplex_prism_position 2 (a j) (t0 j))).
    rewrite simplex_prism_position_rank, ordinal_next_rank.
    pose proof (simplex_prism_pivot_upper a t1 j E) as H.
    assert (F : fin_rank (t0 j) = 1).
    { change (fin_rank (@fin_merge 1 (fin_first : Ordinal 1) (b j)) = 1) in E.
      change (fin_rank (@fin_merge 1 (fin_first⁺ : Ordinal 1) (b j)) = 1).
      destruct (b j) as [[] | [[] | [[] | []]]]; cbn in *; lia. }
    rewrite F. unfold l. lia. }
  pose proof (simplex_prism_factor_space l⁺ c t1 H0 H1) as E.
  pose proof (simplex_prism_factor_time l⁺ c t1 H0 H1) as F.
  pose proof (simplex_prism_factor_space k a t0
    (simplex_prism_pivot_lower a t0) (simplex_prism_pivot_upper a t0)) as G.
  pose proof (simplex_prism_factor_time k a t0
    (simplex_prism_pivot_lower a t0) (simplex_prism_pivot_upper a t0)) as J.
  exists (simplex_triangle_product_index k l), h.
  unfold SimplexTriangleProductSpaceF, SimplexTriangleProductTimeF.
  rewrite (simplex_triangle_product_index_pivots k l
    simplex_triangle_product_pivot_order). cbn [fst snd].
  split; apply (snd (simplex_eq_iff _ _)); intros z.
  - pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
    pose proof (fst (simplex_eq_iff _ _) G z) as Gz.
    change (σ[2; k] (σ[3; l⁺] (h z)) = a z).
    change (σ[3; l⁺] (h z) = c z) in Ez.
    change (σ[2; k] (c z) = a z) in Gz.
    rewrite Ez. exact Gz.
  - apply (@fin_rank_injective 3).
    change (fin_rank (@simplex_prism_position 1
      (SimplexPrismTimeF k (σ[3; l⁺] (h z)))
      (SimplexPrismTimeF l⁺ (h z))) = fin_rank (b z)).
    rewrite simplex_prism_position_rank.
    pose proof (fst (simplex_eq_iff _ _) E z) as Ez.
    pose proof (fst (simplex_eq_iff _ _) F z) as Fz.
    pose proof (fst (simplex_eq_iff _ _) J z) as Jz.
    change (σ[3; l⁺] (h z) = c z) in Ez.
    change (SimplexPrismTimeF l⁺ (h z) = t1 z) in Fz.
    change (SimplexPrismTimeF k (c z) = t0 z) in Jz.
    rewrite Ez, Fz, Jz.
    change (fin_rank (@fin_merge 1 (fin_first⁺ : Ordinal 1) (b z)) +
      fin_rank (@fin_merge 1 (fin_first : Ordinal 1) (b z)) = fin_rank (b z)).
    destruct (b z) as [[] | [[] | [[] | []]]]; reflexivity.
Defined.

End ProductFactor.

(** Any two factors with the same two coordinates agree in specified
    operator equality, even if their staircase indices differ. *)

(** 即使阶梯索引不同，同样双坐标的两个因子也按指定算子相等一致。 *)

Lemma simplex_triangle_product_factors_eq {n : nat} (i j : Ordinal 5)
    (f g : (@Hom Δ) n 4)
    (E : SimplexTriangleProductSpaceF i ∘ f ≈
      SimplexTriangleProductSpaceF j ∘ g)
    (F : SimplexTriangleProductTimeF i ∘ f ≈
      SimplexTriangleProductTimeF j ∘ g)
  : f ≈ g.
Proof.
  apply simplex_eq_of_rank. intros z.
  pose proof (simplex_triangle_product_coordinate_rank i (f z)) as H.
  pose proof (simplex_triangle_product_coordinate_rank j (g z)) as J.
  pose proof (f_equal fin_rank (fst (simplex_eq_iff _ _) E z)) as A.
  pose proof (f_equal fin_rank (fst (simplex_eq_iff _ _) F z)) as B.
  change (fin_rank (SimplexTriangleProductSpaceF i (f z)) =
    fin_rank (SimplexTriangleProductSpaceF j (g z))) in A.
  change (fin_rank (SimplexTriangleProductTimeF i (f z)) =
    fin_rank (SimplexTriangleProductTimeF j (g z))) in B.
  lia.
Defined.
