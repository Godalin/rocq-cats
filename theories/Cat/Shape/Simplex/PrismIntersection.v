From Cats Require Export
  Cat.Shape.Simplex.Prism.
From Cats Require Import
  Cat.Core.
From Stdlib Require Import
  Arith.PeanoNat
  Lia.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Intersections of Staircase Simplices

    The constructive cover
    %\coqref{Cats.Cat.Shape.Simplex.Prism.SimplexPrismFactor}
    {%[SimplexPrismFactor]%}% does not assert that supplied values agree
    on overlaps. Here two actual coordinate equations determine their
    common factor. For adjacent staircases that factor omits the shared
    diagonal position and hence passes through one common coface. The
    mediator is the existing [CofacePreimageF], including in high degrees. *)

(** * 阶梯单形的交叠

    构造性覆盖 %\coqref{Cats.Cat.Shape.Simplex.Prism.SimplexPrismFactor}
    {%[SimplexPrismFactor]%}% 不保证给定值在交叠上相容。此处由两个实际
    坐标方程确定共同因子。相邻阶梯的因子省略共享对角位置，因此经过同一
    余面；中介复用既有 [CofacePreimageF]，也适用于高维。 *)

(** When both coordinate equations hold for adjacent pivots, the two
    triangles below commute in specified operator equality. The dashed
    mediator is constructed, not supplied as another assumption; both
    appearances of δ omit position [i+1]. The subscripts distinguish
    two staircase copies of the same ordinal shape. *)

(** 相邻枢轴满足两个坐标方程时，下方两个三角形按指定算子相等交换。虚线
    中介由构造给出，不是另一个假设；两处 δ 均省略位置 [i+1]。下标仅区分
    同一序数形状的两个阶梯副本。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
& {[n]} \arrow[dl,"f"'] \arrow[d,dashed,"h"] \arrow[dr,"g"] & \\
{[m+2]_{i}} & {[m+1]} \arrow[l,"{\delta_{i+1}}"]
  \arrow[r,"{\delta_{i+1}}"'] & {[m+2]_{i+1}}
\end{tikzcd}
\end{center}%
*)

(** Equal spatial and temporal coordinates force equal factor operators,
    even when the two staircases have different pivots. *)

(** 即使阶梯枢轴不同，相同空间及时间坐标也迫使因子算子相等。 *)

Lemma simplex_prism_factors_eq {n m : nat} (i j : Ordinal m)
    (f g : (@Hom Δ) n (S m))
    (E : σ[m; i] ∘ f ≈ σ[m; j] ∘ g)
    (F : SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g)
  : f ≈ g.
Proof.
  transitivity (SimplexPrismIndexF (σ[m; i] ∘ f)
    (SimplexPrismTimeF i ∘ f)).
  - exact (simplex_prism_factor_unique i _ _ f
      (reflexivity _) (reflexivity _)).
  - symmetry. exact (simplex_prism_factor_unique j _ _ g
      (symmetry E) (symmetry F)).
Defined.

(** The shared face has identity spatial coordinate on both sides. *)

(** 共享面在两侧的空间坐标都为恒等。 *)

Lemma simplex_prism_adjacent_space {m : nat} (i : Ordinal m)
  : σ[S m; i↑] ∘ δ[S m; i↑⁺] ≈ σ[S m; i⁺] ∘ δ[S m; i↑⁺].
Proof.
  transitivity (@Cat.Core.id Δ (S m)).
  - exact (@codegeneracy_coface_next (S m) i↑).
  - symmetry. exact (@codegeneracy_coface_id (S m) i⁺).
Defined.

(** Both time coordinates agree on that same shared face. *)

(** 两个时间坐标在同一共享面上一致。 *)

Lemma simplex_prism_adjacent_time {m : nat} (i : Ordinal m)
  : SimplexPrismTimeF i↑ ∘ δ[S m; i↑⁺] ≈
      SimplexPrismTimeF i⁺ ∘ δ[S m; i↑⁺].
Proof.
  apply (snd (simplex_eq_iff _ _)). intros j.
  change ((if Nat.ltb (fin_rank i↑) (fin_rank (@fin_skip (S (S m)) i↑⁺ j))
      then (fin_first⁺ : Ordinal 1) else fin_first) =
    (if Nat.ltb (fin_rank i⁺) (fin_rank (@fin_skip (S (S m)) i↑⁺ j))
      then (fin_first⁺ : Ordinal 1) else fin_first)).
  rewrite fin_skip_rank, !ordinal_next_rank, !ordinal_weaken_rank.
  unfold skip_rank.
  repeat match goal with
  | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb_spec0 x y)
  end; try reflexivity; exfalso;
    repeat match goal with
    | H : context [Nat.ltb ?x ?y] |- _ => destruct (Nat.ltb_spec0 x y)
    end; lia.
Defined.

(** ** Factoring an Arbitrary Adjacent Overlap

    Fix any source degree, spatial dimension and adjacent pivot pair.
    Both supplied coordinate equations are required. They identify the
    two factor operators and exclude the shared omitted position. No
    choice or equality of factorization witnesses is assumed. *)

(** ** 分解任意相邻交叠

    固定任意来源维数、空间维数及相邻枢轴对。需要两个给定坐标方程；它们
    识别两个因子算子并排除共享省略位置。不假设选择或分解见证相等。 *)

Section AdjacentOverlap.
Context {n m : nat} (i : Ordinal m)
    (f g : (@Hom Δ) n (S (S m))).
Context (E : σ[S m; i↑] ∘ f ≈ σ[S m; i⁺] ∘ g).
Context (F : SimplexPrismTimeF i↑ ∘ f ≈ SimplexPrismTimeF i⁺ ∘ g).

(** Every common factor goes through the actual shared coface. *)

(** 每个共同因子都经过实际共享余面。 *)

Definition SimplexPrismAdjacentFactor
  : ∃ h : (@Hom Δ) n (S m),
      (δ[S m; i↑⁺] ∘ h ≈ f) ∧ (δ[S m; i↑⁺] ∘ h ≈ g).
Proof.
  pose proof (simplex_prism_factors_eq i↑ i⁺ f g E F) as G.
  assert (H : ∀ z, ¬ f z = i↑⁺).
  { intros z H.
    pose proof (fst (simplex_eq_iff _ _) F z) as T.
    pose proof (fst (simplex_eq_iff _ _) G z) as V.
    change (SimplexPrismTimeF i↑ (f z) = SimplexPrismTimeF i⁺ (g z)) in T.
    rewrite <- V, H in T.
    change ((if Nat.ltb (fin_rank i↑) (fin_rank i↑⁺)
        then (fin_first⁺ : Ordinal 1) else fin_first) =
      (if Nat.ltb (fin_rank i⁺) (fin_rank i↑⁺)
        then (fin_first⁺ : Ordinal 1) else fin_first)) in T.
    rewrite !ordinal_next_rank, !ordinal_weaken_rank in T.
    destruct (Nat.ltb_spec0 (fin_rank i) (S (fin_rank i)));
      destruct (Nat.ltb_spec0 (S (fin_rank i)) (S (fin_rank i)));
      try lia; discriminate T. }
  exists (CofacePreimageF i↑⁺ f H). split.
  - apply coface_preimage_β.
  - transitivity f; [apply coface_preimage_β | exact G].
Defined.

End AdjacentOverlap.

(** ** The Outer Intersection of a Triangle Cylinder

    For the three triangle staircases, the first and last meet along an
    edge also contained in the middle staircase. Coordinate equality
    makes their common factor avoid both internal positions. This lets
    adjacent compatibility equations control the nonadjacent pair. *)

(** ** 三角柱的首尾交叠

    三个三角阶梯的首尾两块沿一条边相交，该边也在中间阶梯内。坐标相等使
    共同因子避开两个内部位置，因此相邻相容方程也能控制不相邻的一对。 *)

Lemma simplex_prism_outer_middle {n : nat}
    (f g : (@Hom Δ) n 3)
    (E : σ[2; fin_first] ∘ f ≈ σ[2; fin_first⁺⁺] ∘ g)
    (F : SimplexPrismTimeF fin_first ∘ f ≈
      SimplexPrismTimeF fin_first⁺⁺ ∘ g)
  : (σ[2; fin_first] ∘ f ≈ σ[2; fin_first⁺] ∘ f) ∧
      (SimplexPrismTimeF fin_first ∘ f ≈ SimplexPrismTimeF fin_first⁺ ∘ f).
Proof.
  pose proof (simplex_prism_factors_eq fin_first fin_first⁺⁺ f g E F) as G.
  assert (H : ∀ z,
      σ[2; fin_first] (f z) = σ[2; fin_first⁺⁺] (f z)).
  { intros z. pose proof (fst (simplex_eq_iff _ _) E z) as H.
    pose proof (fst (simplex_eq_iff _ _) G z) as V.
    change (σ[2; fin_first] (f z) = σ[2; fin_first⁺⁺] (g z)) in H.
    now rewrite <- V in H. }
  split; apply (snd (simplex_eq_iff _ _)); intros z.
  - change (σ[2; fin_first] (f z) = σ[2; fin_first⁺] (f z)).
    specialize (H z). destruct (f z) as [[] | [[] | [[] | [[] | []]]]];
      try reflexivity; discriminate H.
  - change (SimplexPrismTimeF fin_first (f z) =
      SimplexPrismTimeF fin_first⁺ (f z)).
    specialize (H z). destruct (f z) as [[] | [[] | [[] | [[] | []]]]];
      try reflexivity; discriminate H.
Defined.
