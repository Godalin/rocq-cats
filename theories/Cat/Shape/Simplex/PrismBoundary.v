From Cats Require Export
  Cat.Shape.Simplex.Prism.
From Cats Require Import
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * The Six Outer Triangles of a Triangle Prism

    Each spatial boundary edge has two staircase triangles. The pair
    below records the actual prism piece and its coface; both coordinates
    agree with the boundary-edge inclusion. No geometric realization or
    filling choice is involved. *)

(** * 三角棱柱的六个外侧三角形

    每条空间边界边有两个阶梯三角形。下方的二元组记录实际棱柱块与余面；
    两个坐标都与边界边包含映射一致，不涉及几何实现或填充选择。 *)

(** Rows are the omitted spatial vertices; columns are the edge's two
    staircase indices. Entries are (prism piece, omitted prism vertex). *)

(** 行表示遗漏的空间顶点，列表示边的两个阶梯索引；表项为棱柱块及遗漏顶点。 *)

Definition simplex_triangle_prism_side (j : Ordinal 2) (k : Ordinal 1)
  : Ordinal 2 * Ordinal 3.
Proof.
  destruct j as [[] | [[] | [[] | []]]], k as [[] | [[] | []]].
  - exact (fin_first⁺, fin_first).
  - exact (fin_first⁺⁺, fin_first).
  - exact (fin_first, fin_first⁺⁺).
  - exact (fin_first⁺⁺, fin_first⁺).
  - exact (fin_first, fin_first⁺⁺⁺).
  - exact (fin_first⁺, fin_first⁺⁺⁺).
Defined.

(** Restricting the indicated prism face recovers the spatial edge map. *)

(** 限制所示棱柱面，恢复空间边映射。 *)

Lemma simplex_triangle_prism_side_space (j : Ordinal 2) (k : Ordinal 1)
  : σ[2; fst (simplex_triangle_prism_side j k)] ∘
      δ[2; snd (simplex_triangle_prism_side j k)] ≈ δ[1; j] ∘ σ[1; k].
Proof.
  apply (snd (simplex_eq_iff _ _)). intros i.
  destruct j as [[] | [[] | [[] | []]]], k as [[] | [[] | []]],
    i as [[] | [[] | [[] | []]]]; reflexivity.
Defined.

(** The same restriction recovers the edge's staircase time coordinate. *)

(** 同一限制恢复边的阶梯时间坐标。 *)

Lemma simplex_triangle_prism_side_time (j : Ordinal 2) (k : Ordinal 1)
  : SimplexPrismTimeF (fst (simplex_triangle_prism_side j k)) ∘
      δ[2; snd (simplex_triangle_prism_side j k)] ≈ SimplexPrismTimeF k.
Proof.
  apply (snd (simplex_eq_iff _ _)). intros i.
  destruct j as [[] | [[] | [[] | []]]], k as [[] | [[] | []]],
    i as [[] | [[] | [[] | []]]]; reflexivity.
Defined.
