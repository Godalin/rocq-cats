From Cats Require Export
  Cat.Shape.Simplex.Operators.
From Cats.Set Require Import
  OrdinalMaximum.
From Cats Require Import
  Cat.Core.
From Stdlib Require Import
  Arith.PeanoNat
  Lia.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Staircase Simplices Cover a Simplex Cylinder

    A simplex in [Δ[m] × Δ[1]] consists of two monotone operators a and t
    with the same source. Choose the largest spatial vertex occurring at
    time zero, or zero if there is none. This pivot k places every point
    on the staircase which repeats spatial vertex k and changes time
    there. The factor has rank [a(j) + t(j)]. Repeated positions and
    arbitrarily high source dimensions require no special cases.

    This is a constructive statement about shape operators, not yet a
    gluing theorem for values in an arbitrary simplicial setoid. In
    particular it does not reconstruct a relative sphere cylinder. *)

(** * 阶梯单形覆盖单形柱

    [Δ[m] × Δ[1]] 的一个单形由同源的两个保序算子 a、t 组成。选择时间零
    处出现的最大空间顶点，无此顶点时取零。该枢轴 k 使每个点落在重复空间
    顶点 k 并于该处切换时间的阶梯上。分解因子的编号为 [a(j) + t(j)]。
    允许重复位置及任意高的来源维数，无需特殊处理。

    这是形状算子的构造性结论，尚非任意单纯广集取值的粘合定理，尤其尚不
    重构相对球面柱。 *)

(** In the diagram the two triangles commute in the specified equality
    of Δ. For m=2 these are the three tetrahedra of a triangle cylinder. *)

(** 图中两个三角形按 Δ 的指定相等交换。m=2 时，这些阶梯恰是三角柱的三个
    四面体。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
& {[m+1]} \arrow[dl,"{\sigma_k}"'] \arrow[dr,"{\tau_k}"] & \\
{[m]} & {[n]} \arrow[l,"a"] \arrow[u,dashed,"h"] \arrow[r,"t"'] & {[1]}
\end{tikzcd}
\end{center}%
*)

(** Time zero uses the first copy of a spatial position; time one uses
    its successor copy. The result is independent of any chosen pivot. *)

(** 时间零使用空间位置的首份副本，时间一使用后继副本；结果不依赖枢轴选择。 *)

Definition simplex_prism_position {m : nat} (a : Ordinal m) (t : Ordinal 1)
  : Ordinal (S m)
  := if Nat.eqb (fin_rank t) 0 then a↑ else a⁺.

(** The interleaved position adds the spatial and temporal ranks. *)

(** 交织位置的编号为空间与时间编号之和。 *)

Lemma simplex_prism_position_rank {m : nat} (a : Ordinal m) (t : Ordinal 1)
  : fin_rank (simplex_prism_position a t) = fin_rank a + fin_rank t.
Proof.
  destruct t as [[] | [[] | []]].
  - change (fin_rank a↑ = fin_rank a + 0).
    rewrite ordinal_weaken_rank. lia.
  - change (fin_rank a⁺ = fin_rank a + 1).
    rewrite ordinal_next_rank. lia.
Defined.

(** Interleaving two monotone operators is again monotone. *)

(** 两个保序算子的交织仍然保序。 *)

Program Definition SimplexPrismIndexF {n m : nat}
    (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : (@Hom Δ) n (S m)
  := OrdinalF (λ j, simplex_prism_position (a j) (t j)) _.
Next Obligation.
  change (fin_rank (simplex_prism_position (a x) (t x)) ≤
    fin_rank (simplex_prism_position (a y) (t y))).
  rewrite !simplex_prism_position_rank.
  pose proof (ordinal_fct_monotone a x y H).
  pose proof (ordinal_fct_monotone t x y H). lia.
Defined.

(** Restriction commutes with the interleaved factor. The pivot selected
    for the restricted simplex may change; its factor formula does not. *)

(** 限制与交织因子交换。受限单形选出的枢轴可以改变，但其因子公式不变。 *)

Lemma simplex_prism_index_pre {r n m : nat} (θ : (@Hom Δ) r n)
    (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : SimplexPrismIndexF (a ∘ θ) (t ∘ θ) ≈ SimplexPrismIndexF a t ∘ θ.
Proof. apply (snd (simplex_eq_iff _ _)). intros j. reflexivity. Defined.

(** Staircase time changes immediately after the pivot's first copy. *)

(** 阶梯时间在枢轴的首份副本之后立即切换。 *)

Program Definition SimplexPrismTimeF {m : nat} (k : Ordinal m)
  : (@Hom Δ) (S m) 1%nat
  := OrdinalF
      (λ j, if Nat.ltb (fin_rank k) (fin_rank j)
        then (fin_first⁺ : Ordinal 1) else fin_first) _.
Next Obligation.
  change (@fin_rank (S (S m)) x ≤ @fin_rank (S (S m)) y) in H.
  change (fin_rank (if Nat.ltb (@fin_rank (S m) k)
      (@fin_rank (S (S m)) x) then (fin_first⁺ : Ordinal 1)
      else fin_first) ≤
    fin_rank (if Nat.ltb (@fin_rank (S m) k)
      (@fin_rank (S (S m)) y) then (fin_first⁺ : Ordinal 1)
      else fin_first)).
  destruct (Nat.ltb_spec0 (@fin_rank (S m) k) (@fin_rank (S (S m)) x));
    destruct (Nat.ltb_spec0 (@fin_rank (S m) k) (@fin_rank (S (S m)) y));
    cbn in *; lia.
Defined.

(** ** Finding a Staircase from Arbitrary Coordinates

    Fix arbitrary dimensions and monotone spatial/time operators. Finite
    maxima compute the pivot. Monotonicity forces every time-one spatial
    image above every time-zero image, so this single pivot separates them. *)

(** ** 从任意坐标寻找阶梯

    固定任意维数及保序空间／时间算子，以有限最大值计算枢轴。保序性迫使
    时间一处的每个空间像不低于时间零处的每个像，因此单个枢轴即可分隔两者。 *)

Section PrismCoordinates.
Context {n m : nat} (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat).

(** Take the maximum of time-zero images, replacing time-one images by
    zero. This also handles a time coordinate which is constantly one. *)

(** 取时间零的像之最大值，将时间一的像替为零；也处理时间恒为一的情形。 *)

Definition simplex_prism_pivot
  : Ordinal m
  := finite_ordinal_max (S n)
      (λ j, if Nat.eqb (fin_rank (t j)) 0 then a j else fin_first).

(** Each time-zero image is bounded by the pivot. *)

(** 每个时间零的像均不超过枢轴。 *)

Lemma simplex_prism_pivot_lower (j : Ordinal n) (E : fin_rank (t j) = 0)
  : fin_rank (a j) ≤ fin_rank simplex_prism_pivot.
Proof.
  pose proof (finite_ordinal_max_upper
    (λ i, if Nat.eqb (fin_rank (t i)) 0 then a i else fin_first) j) as H.
  change (fin_rank (if Nat.eqb (fin_rank (t j)) 0
      then a j else fin_first) ≤ fin_rank simplex_prism_pivot) in H.
  rewrite E in H. exact H.
Defined.

(** Each time-one image bounds the pivot, including its zero default. *)

(** 每个时间一的像均为枢轴的上界，也约束其默认零值。 *)

Lemma simplex_prism_pivot_upper (j : Ordinal n) (E : fin_rank (t j) = 1)
  : fin_rank simplex_prism_pivot ≤ fin_rank (a j).
Proof.
  apply finite_ordinal_max_bound. intros i.
  destruct (Nat.eqb_spec (fin_rank (t i)) 0) as [F | F].
  - assert (H : fin_rank i ≤ fin_rank j).
    { destruct (Nat.le_ge_cases (fin_rank i) (fin_rank j)) as [H | H].
      - exact H.
      - pose proof (ordinal_fct_monotone t j i H). lia. }
    exact (ordinal_fct_monotone a i j H).
  - cbn. lia.
Defined.

End PrismCoordinates.

(** ** Coordinate Equations for Any Admissible Pivot

    An arbitrary pivot works whenever zero-time spatial values lie below
    it and one-time values lie above it. The same interleaved index then
    factors both coordinates. No equality of operator records is used. *)

(** ** 任意合适枢轴的坐标方程

    只要时间零的空间值不超过枢轴、时间一的值不低于枢轴，该枢轴就适用。
    同一交织索引同时分解两个坐标，不使用算子记录相等。 *)

Section PrismFactorEquations.
Context {n m : nat} (k : Ordinal m)
    (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat).
Context (H0 : ∀ j, fin_rank (t j) = 0 → fin_rank (a j) ≤ fin_rank k).
Context (H1 : ∀ j, fin_rank (t j) = 1 → fin_rank k ≤ fin_rank (a j)).

(** The staircase's spatial codegeneracy recovers a. *)

(** 阶梯的空间余退化恢复 a。 *)

Lemma simplex_prism_factor_space
  : σ[m; k] ∘ SimplexPrismIndexF a t ≈ a.
Proof.
  apply simplex_eq_of_rank. intros j.
  change (fin_rank (fin_merge k (simplex_prism_position (a j) (t j))) =
    fin_rank (a j)).
  rewrite fin_merge_rank, simplex_prism_position_rank.
  specialize (H0 j). specialize (H1 j).
  destruct (t j) as [[] | [[] | []]]; cbn [fin_rank] in *;
    unfold merge_rank;
    repeat match goal with
    | |- context [Nat.leb ?x ?y] => destruct (Nat.leb_spec0 x y)
    end; lia.
Defined.

(** The staircase's time operator recovers t. *)

(** 阶梯的时间算子恢复 t。 *)

Lemma simplex_prism_factor_time
  : SimplexPrismTimeF k ∘ SimplexPrismIndexF a t ≈ t.
Proof.
  apply simplex_eq_of_rank. intros j.
  change (fin_rank (if Nat.ltb (fin_rank k)
    (fin_rank (simplex_prism_position (a j) (t j)))
    then (fin_first⁺ : Ordinal 1) else fin_first) = fin_rank (t j)).
  rewrite simplex_prism_position_rank.
  specialize (H0 j). specialize (H1 j).
  destruct (t j) as [[] | [[] | []]]; cbn [fin_rank] in *;
    repeat match goal with
    | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb_spec0 x y)
    end; cbn; lia.
Defined.

End PrismFactorEquations.

(** Compute a staircase and an actual monotone factor for every simplex
    of the product, retaining both specified coordinate equations. *)

(** 为积的每个单形计算阶梯及实际保序因子，并保留两个指定坐标方程。 *)

Definition SimplexPrismFactor {n m : nat}
    (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
  : ∃ k : Ordinal m, ∃ h : (@Hom Δ) n (S m),
      ((σ[m; k] ∘ h ≈ a) * (SimplexPrismTimeF k ∘ h ≈ t))%type.
Proof.
  exists (simplex_prism_pivot a t), (SimplexPrismIndexF a t).
  split.
  - exact (simplex_prism_factor_space (simplex_prism_pivot a t) a t
      (simplex_prism_pivot_lower a t) (simplex_prism_pivot_upper a t)).
  - exact (simplex_prism_factor_time (simplex_prism_pivot a t) a t
      (simplex_prism_pivot_lower a t) (simplex_prism_pivot_upper a t)).
Defined.

(** Space and time together determine the staircase position by adding
    their ranks, even where two different staircases overlap. *)

(** 空间与时间的编号之和确定阶梯位置，两个不同阶梯交叠处也成立。 *)

Lemma simplex_prism_coordinate_rank {m : nat} (k : Ordinal m)
    (j : Ordinal (S m))
  : fin_rank j = fin_rank (σ[m; k] j) + fin_rank (SimplexPrismTimeF k j).
Proof.
  change (fin_rank j = fin_rank (fin_merge k j) +
    fin_rank (if Nat.ltb (fin_rank k) (fin_rank j)
      then (fin_first⁺ : Ordinal 1) else fin_first)).
  rewrite fin_merge_rank. unfold merge_rank.
  destruct (Nat.leb_spec0 (fin_rank j) (fin_rank k));
    destruct (Nat.ltb_spec0 (fin_rank k) (fin_rank j));
    cbn [fin_rank ordinal_next ordinal_weaken fin_first fin_next].
  all: try lia.
  change (fin_rank j = Nat.pred (fin_rank j) + 1). lia.
Defined.

(** Any supplied staircase factor agrees with the canonical interleaved
    factor. This compares operators by specified equality, not records or
    factorization witnesses; different admissible pivots are allowed. *)

(** 任意给定阶梯因子都与规范交织因子一致。用指定相等比较算子，不比较记录或
    分解见证，并允许不同的合适枢轴。 *)

Lemma simplex_prism_factor_unique {n m : nat} (k : Ordinal m)
    (a : (@Hom Δ) n m) (t : (@Hom Δ) n 1%nat)
    (h : (@Hom Δ) n (S m))
    (E : σ[m; k] ∘ h ≈ a) (F : SimplexPrismTimeF k ∘ h ≈ t)
  : h ≈ SimplexPrismIndexF a t.
Proof.
  apply simplex_eq_of_rank. intros j.
  pose proof (simplex_prism_coordinate_rank k (h j)) as H.
  pose proof (f_equal fin_rank (fst (simplex_eq_iff _ _) E j)) as A.
  pose proof (f_equal fin_rank (fst (simplex_eq_iff _ _) F j)) as T.
  change (fin_rank (h j) =
    fin_rank (simplex_prism_position (a j) (t j))).
  rewrite simplex_prism_position_rank.
  change (fin_rank (σ[m; k] (h j)) = fin_rank (a j)) in A.
  change (fin_rank (SimplexPrismTimeF k (h j)) = fin_rank (t j)) in T.
  rewrite A, T in H. exact H.
Defined.
