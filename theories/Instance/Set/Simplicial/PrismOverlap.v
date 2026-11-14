From Cats Require Export
  Instance.Set.Simplicial.Prism
  Cat.Shape.Simplex.PrismIntersection.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Adjacent Face Equations Control Prism Overlaps

    The shape mediator in
    %\coqref{Cats.Cat.Shape.Simplex.PrismIntersection.SimplexPrismAdjacentFactor}
    {%[SimplexPrismAdjacentFactor]%}% lets a single adjacent-face equation
    control every pair of common factors. For a triangle cylinder, the
    first/last intersection also lies in the middle piece. Consequently
    just two adjacent-face equations give all overlap equations.

    These are compatibility witnesses for supplied simplex values. This
    module does not yet glue them to a cylinder map or supply Kan fillers. *)

(** * 相邻面方程控制棱柱交叠

    形状中介
    %\coqref{Cats.Cat.Shape.Simplex.PrismIntersection.SimplexPrismAdjacentFactor}
    {%[SimplexPrismAdjacentFactor]%}% 将单个相邻面方程扩展到任意共同因子对。
    三角柱首尾交叠也在中间块内，因此两条相邻面方程就给出全部交叠方程。

    这些是给定单形值的相容见证，本模块尚不将它们粘成柱映射，也不提供 Kan
    填充。 *)

(** ** Restricting the Actual Common Face

    Fix an arbitrary simplicial setoid at independent value sizes. For
    adjacent staircases of any dimension, restrict their supplied face
    equation along the computed mediator. No choice of simplex filler
    or equality of mediator proof fields is needed. *)

(** ** 限制实际共同面

    固定独立取值大小的任意单纯广集。对任意维数的相邻阶梯，沿计算所得中介
    限制给定面方程，无需单形填充选择或中介证明字段相等。 *)

Section AdjacentPrismValues.
Universes u p.
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} {m : nat}.

(** The given equality on the shared face controls arbitrary common
    spatial/time factors, including high-dimensional degenerate ones. *)

(** 给定共享面上的相等控制任意空间／时间共同因子，包括高维退化因子。 *)

Lemma simplex_prism_adjacent_overlap (i : Ordinal m)
    (x y : X (S (S m)))
    (H : d[X; S m; i↑⁺] x ≈S d[X; S m; i↑⁺] y)
    {n : nat} (f g : (@Hom Δ) n (S (S m)))
    (E : σ[S m; i↑] ∘ f ≈ σ[S m; i⁺] ∘ g)
    (F : SimplexPrismTimeF i↑ ∘ f ≈ SimplexPrismTimeF i⁺ ∘ g)
  : X[f]Δ x ≈S X[g]Δ y.
Proof.
  destruct (SimplexPrismAdjacentFactor i f g E F) as [h [Hf Hg]].
  transitivity (X[δ[S m; i↑⁺] ∘ h]Δ x).
  - apply simplex_restrict_proper. symmetry. exact Hf.
  - transitivity (X[h]Δ (d[X; S m; i↑⁺] x)).
    + apply simplex_restrict_comp.
    + transitivity (X[h]Δ (d[X; S m; i↑⁺] y)).
      * apply func_proper. exact H.
      * transitivity (X[δ[S m; i↑⁺] ∘ h]Δ y).
        -- symmetry. apply simplex_restrict_comp.
        -- apply simplex_restrict_proper. exact Hg.
Defined.

(** An actual cylinder map supplies these adjacent equations by
    naturality and the two coordinate equations of the common face. *)

(** 实际柱映射由自然性及共同面的两个坐标方程提供这些相邻方程。 *)

Lemma simplex_prism_values_adjacent
    (K : SimplicialCylinderF
      (Δ[S m] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X)
    (i : Ordinal m)
  : d[X; S m; i↑⁺] (simplex_prism_eval K i↑) ≈S
      d[X; S m; i↑⁺] (simplex_prism_eval K i⁺).
Proof.
  transitivity (K (S m)
    ({|lower := σ[S m; i↑] ∘ δ[S m; i↑⁺]|},
     {|lower := SimplexPrismTimeF i↑ ∘ δ[S m; i↑⁺]|})).
  - symmetry. exact (simplex_restrict_natural K δ[S m; i↑⁺]
      ({|lower := σ[S m; i↑]|}, {|lower := SimplexPrismTimeF i↑|})).
  - transitivity (K (S m)
      ({|lower := σ[S m; i⁺] ∘ δ[S m; i↑⁺]|},
       {|lower := SimplexPrismTimeF i⁺ ∘ δ[S m; i↑⁺]|})).
    + apply func_proper. split; refine {|lower := _|}.
      * apply simplex_prism_adjacent_space.
      * apply simplex_prism_adjacent_time.
    + exact (simplex_restrict_natural K δ[S m; i↑⁺]
        ({|lower := σ[S m; i⁺]|}, {|lower := SimplexPrismTimeF i⁺|})).
Defined.

End AdjacentPrismValues.

(** ** Three Triangle-Prism Values

    Fix three actual tetrahedra and the two adjacent-face equations.
    The nonadjacent pair is compared through the middle tetrahedron;
    this produces all common-factor equations without gluing yet. *)

(** ** 三个三角棱柱值

    固定三个实际四面体及两条相邻面方程。经中间四面体比较首尾两块，在尚未
    粘合的情况下得到全部共同因子方程。 *)

Section TrianglePrismValues.
Universes u p.
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (a : Ordinal 2 → X 3).
Context (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
  d[X; 2; fin_first⁺] (a fin_first⁺)).
Context (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
  d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺)).

(** The outer intersection passes through the middle staircase using
    the same factor on the first two pieces. No output equality is assumed. *)

(** 首尾交叠经过中间阶梯，前两块使用同一因子；不预设最终输出相等。 *)

Lemma simplex_triangle_prism_outer_overlap {n : nat}
    (f g : (@Hom Δ) n 3)
    (E : σ[2; fin_first] ∘ f ≈ σ[2; fin_first⁺⁺] ∘ g)
    (F : SimplexPrismTimeF fin_first ∘ f ≈
      SimplexPrismTimeF fin_first⁺⁺ ∘ g)
  : X[f]Δ (a fin_first) ≈S X[g]Δ (a fin_first⁺⁺).
Proof.
  destruct (simplex_prism_outer_middle f g E F) as [A T].
  transitivity (X[f]Δ (a fin_first⁺)).
  - exact (simplex_prism_adjacent_overlap fin_first _ _ H0 f f A T).
  - exact (simplex_prism_adjacent_overlap fin_first⁺ _ _ H1 f g
      (transitivity (symmetry A) E) (transitivity (symmetry T) F)).
Defined.

(** The two adjacent equations imply compatibility on every common
    factor, in every degree and in both orders of the three pieces. *)

(** 两条相邻方程蕴涵每一维、三个块的两个次序上的任意共同因子相容。 *)

Lemma simplex_triangle_prism_overlap {n : nat} (i j : Ordinal 2)
    (f g : (@Hom Δ) n 3)
    (E : σ[2; i] ∘ f ≈ σ[2; j] ∘ g)
    (F : SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g)
  : X[f]Δ (a i) ≈S X[g]Δ (a j).
Proof.
  destruct i as [[] | [[] | [[] | []]]], j as [[] | [[] | [[] | []]]].
  - apply simplex_restrict_proper. exact (simplex_prism_factors_eq _ _ f g E F).
  - exact (simplex_prism_adjacent_overlap fin_first _ _ H0 f g E F).
  - exact (simplex_triangle_prism_outer_overlap f g E F).
  - symmetry. exact (simplex_prism_adjacent_overlap fin_first _ _ H0 g f
      (symmetry E) (symmetry F)).
  - apply simplex_restrict_proper. exact (simplex_prism_factors_eq _ _ f g E F).
  - exact (simplex_prism_adjacent_overlap fin_first⁺ _ _ H1 f g E F).
  - symmetry. exact (simplex_triangle_prism_outer_overlap g f
      (symmetry E) (symmetry F)).
  - symmetry. exact (simplex_prism_adjacent_overlap fin_first⁺ _ _ H1 g f
      (symmetry E) (symmetry F)).
  - apply simplex_restrict_proper. exact (simplex_prism_factors_eq _ _ f g E F).
Defined.

End TrianglePrismValues.

(** Two adjacent equations are also necessary: specialize all overlaps
    to their actual shared cofaces. Thus this is an exact compatibility
    criterion for three tetrahedra, without asserting gluing existence. *)

(** 两条相邻方程也是必要的：将全部交叠特化到实际共享余面。因此它精确刻画
    三个四面体的相容性，尚不声称粘合存在。 *)

Lemma simplex_triangle_prism_overlap_iff@{u p +}
    {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}} (a : Ordinal 2 → X 3)
  : (∀ n (i j : Ordinal 2) (f g : (@Hom Δ) n 3),
      σ[2; i] ∘ f ≈ σ[2; j] ∘ g →
      SimplexPrismTimeF i ∘ f ≈ SimplexPrismTimeF j ∘ g →
      X[f]Δ (a i) ≈S X[g]Δ (a j)) ↔
      (d[X; 2; fin_first⁺] (a fin_first) ≈S
        d[X; 2; fin_first⁺] (a fin_first⁺)) ∧
      (d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
        d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺)).
Proof.
  split.
  - intros H. split.
    + exact (H 2 fin_first fin_first⁺ δ[2; fin_first⁺] δ[2; fin_first⁺]
        (simplex_prism_adjacent_space fin_first)
        (simplex_prism_adjacent_time fin_first)).
    + exact (H 2 fin_first⁺ fin_first⁺⁺ δ[2; fin_first⁺⁺] δ[2; fin_first⁺⁺]
        (simplex_prism_adjacent_space fin_first⁺)
        (simplex_prism_adjacent_time fin_first⁺)).
  - intros [H0 H1] n i j f g E F.
    exact (simplex_triangle_prism_overlap a H0 H1 i j f g E F).
Defined.
