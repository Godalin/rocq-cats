From Cats Require Export
  Instance.Set.Simplicial.Matching
  Cat.Shape.Simplex.Intersection.
From Cats Require Import
  Cat.Core.
From Stdlib Require Import
  Arith.PeanoNat.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Gluing Faces from Pairwise Equations

    A list of faces usually comes with equations only on their common
    codimension-one faces. Matching descent instead asks for equations on
    every common factor, including degenerate ones of arbitrary degree.
    %\coqref{Cats.Cat.Shape.Simplex.Intersection.CofaceIntersectionFactor}
    {%[CofaceIntersectionFactor]%}% bridges these descriptions: restrict the
    given pairwise equation along its computed mediator. The square below
    commutes in Δ; its dashed map is constructed by that factorization.
    Here v is the position of k inside face j, and w the position of j
    inside face k.

    For a triangle, agreement on a common face means that two edges have
    the same vertex. For a four-simplex, two prescribed tetrahedra must
    agree on a triangle. The construction does not fill the resulting
    boundary or horn. A Kan choice is a separate input at a later stage. *)

(** * 由逐对方程粘合面

    给出一列面时，通常只验证它们在共同的余维一面上相等；匹配下降则要求
    在每个共同因子上相等，包括任意维度的退化因子。
    %\coqref{Cats.Cat.Shape.Simplex.Intersection.CofaceIntersectionFactor}
    {%[CofaceIntersectionFactor]%}%
    连接这两种描述：沿计算得到的中介限制给定逐对方程。下图在 Δ 中交换；
    虚线中介由该分解构造。v 是 k 在面 j 内的位置，w 是 j 在面 k 内的位置。

    对三角形，共同面上的一致意味着两条边在同一个顶点相接；对四维单形，
    两个给定四面体须在交叠三角形上一致。此构造不填充所得边界或 horn，
    Kan 选择是后续单独的输入。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
{[m]} \arrow[dr,dashed,"h"'] \arrow[drr,bend left=15,"f"]
  \arrow[ddr,bend right=15,"g"'] & & \\
& {[n]} \arrow[r,"{\delta_v}"] \arrow[d,"{\delta_w}"']
  & {[n+1]} \arrow[d,"{\delta_j}"] \\
& {[n+1]} \arrow[r,"{\delta_k}"'] & {[n+2]}
\end{tikzcd}
\end{center}%
*)

(** ** Extending One Intersection Equation

    Fix a simplicial setoid at independent carrier and equality sizes.
    Distinct faces j and k have computed local indices v and w. A single
    equation between those faces extends to every equal common factor. *)

(** ** 扩展一个交叠方程

    固定载体与相等大小独立的单纯广集。不同面 j、k 具有计算得到的局部索引
    v、w；两面在该交叠上的一个方程扩展为每个相等共同因子上的方程。 *)

Section PairwiseOverlap.
Universes u p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

(** Restrict a pairwise equation along the common-factor mediator. *)

(** 沿共同因子中介限制逐对方程。 *)

Lemma simplex_pairwise_overlap {m n : nat}
    (j k : Ordinal (S (S n))) (H : ¬ j = k)
    (x y : X (S n))
    (Hxy : d[X; n; coface_intersection_index j k H] x ≈S
      d[X; n; coface_intersection_index k j (λ E, H (symmetry E))] y)
    (f g : (@Hom Δ) m (S n))
    (E : δ[S n; j] ∘ f ≈ δ[S n; k] ∘ g)
  : X[f]Δ x ≈S X[g]Δ y.
Proof.
  destruct (CofaceIntersectionFactor j k H f g E) as [h [Hf Hg]].
  transitivity (X[δ[n; coface_intersection_index j k H] ∘ h]Δ x).
  - apply simplex_restrict_proper. symmetry. exact Hf.
  - transitivity (X[h]Δ
      (d[X; n; coface_intersection_index j k H] x)).
    + apply simplex_restrict_comp.
    + transitivity (X[h]Δ
        (d[X; n; coface_intersection_index k j
          (λ F, H (symmetry F))] y)).
      * apply func_proper. exact Hxy.
      * transitivity (X[δ[n; coface_intersection_index k j
          (λ F, H (symmetry F))] ∘ h]Δ y).
        -- symmetry. apply simplex_restrict_comp.
        -- apply simplex_restrict_proper. exact Hg.
Defined.

(** The faces of an actual simplex satisfy precisely these equations.
    This follows from the intersection square in Δ, rather than any Kan
    structure on X. *)

(** 实际单形的各面恰好满足这些方程；这由 Δ 中的交叠方块导出，无需 X 的
    Kan 结构。 *)

Lemma simplex_faces_pairwise {n : nat} (z : X (S (S n)))
    (j k : Ordinal (S (S n))) (E : ¬ j = k)
  : d[X; n; coface_intersection_index j k E]
      (d[X; S n; j] z) ≈S
      d[X; n; coface_intersection_index k j
        (λ F, E (symmetry F))] (d[X; S n; k] z).
Proof.
  transitivity (X[δ[S n; j] ∘ δ[n;
    coface_intersection_index j k E]]Δ z).
  - symmetry. apply simplex_restrict_comp.
  - transitivity (X[δ[S n; k] ∘ δ[n;
      coface_intersection_index k j (λ F, E (symmetry F))]]Δ z).
    + apply simplex_restrict_proper. exact (coface_intersection_swap j k E).
    + apply simplex_restrict_comp.
Defined.

End PairwiseOverlap.

(** ** Selecting Faces and Descending

    A Type-valued predicate P specifies which faces are retained. Values
    depend on the index, while equations may use the membership witnesses.
    No equality between those witnesses is imposed. This single matching
    construction serves horns; all-face boundaries use the same overlap
    lemma below. The ambient simplex has dimension at least two. *)

(** ** 选取面并下降

    Type 值谓词 P 指定保留哪些面。面的值依赖索引，方程可以使用成员见证，
    但不等同这些见证。下述统一匹配构造用于 horn，全体面组成的边界则复用
    同一交叠引理。环境单形的维度至少为二。 *)

Section FaceGluing.
Universes u p r.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (n : nat).

(** Pairwise compatibility suffices for every generated-sieve overlap.
    Unretained values of a impose no condition. *)

(** 逐对相容足以给出生成筛的全部交叠；a 的未保留项不施加条件。 *)

Program Definition CofaceFacesMatching
    (P : Ordinal (S (S n)) → Type@{r})
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k, P j → P k → ∀ E : ¬ j = k,
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
  : @SieveMatchingS Δ (S (S n)) (∃ j, P j)
      (λ _, S n) (λ j, δ[S n; j.1]) X
  :=
  {|matching_value j := a j.1
  |}.
Next Obligation.
  destruct i as [j0 Hj], j as [k Hk].
  rename j0 into j.
  destruct (Nat.eq_dec (@fin_rank (S (S (S n))) j)
    (@fin_rank (S (S (S n))) k)) as [F | F].
  - pose proof (@fin_rank_injective (S (S (S n))) j k F) as G. subst k.
    apply simplex_restrict_proper.
    apply (snd (simplex_eq_iff _ _)). intros z.
    apply (@fin_skip_injective (S (S n)) j).
    exact (fst (simplex_eq_iff _ _) E z).
  - assert (Hjk : ¬ j = k) by (intros G; subst k; destruct (F eq_refl)).
    exact (simplex_pairwise_overlap X j k Hjk (a j) (a k)
      (H j k Hj Hk Hjk) f h E).
Defined.

(** Actual horn descent uses only pairwise equations between retained
    faces; the omitted entry is a placeholder. *)

(** 实际 horn 下降只使用保留面之间的逐对方程；缺失项只是占位。 *)

Definition HornFacesN (i : Ordinal (S (S n)))
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k, ¬ j = i → ¬ k = i → ∀ E : ¬ j = k,
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
  : HornS X (S (S n)) i
  := SieveMatchingN _ _ (CofaceFacesMatching (λ j, ¬ j = i) a H).

(** Retained faces recover exactly the prescribed values in X. *)

(** 保留面按 X 的指定相等恢复给定值。 *)

Lemma horn_faces_β (i : Ordinal (S (S n)))
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k, ¬ j = i → ¬ k = i → ∀ E : ¬ j = k,
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
    (j : Ordinal (S (S n))) (Hj : ¬ j = i)
  : face[i; j; Hj] (HornFacesN i a H) ≈S a j.
Proof. apply simplex_restrict_id. Defined.

(** A map with the prescribed retained faces is the descended horn map.
    Reuse generator equality; naturality fields are never compared. *)

(** 具有给定保留面的映射等于下降所得 horn 映射。复用生成元判等，不比较
    自然性字段。 *)

Lemma horn_faces_unique (i : Ordinal (S (S n)))
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k, ¬ j = i → ¬ k = i → ∀ E : ¬ j = k,
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
    (h : HornS X (S (S n)) i)
    (E : ∀ j (Hj : ¬ j = i), face[i; j; Hj] h ≈S a j)
  : HornFacesN i a H ≈S h.
Proof.
  apply (snd (@generated_sieve_map_eq Δ (S (S n))
    (∃ j : Ordinal (S (S n)), ¬ j = i) (λ _, S n)
    (λ j, δ[S n; j.1]) X _ _)).
  intros [j Hj]. transitivity (a j).
  - apply horn_faces_β.
  - symmetry. exact (E j Hj).
Defined.

(** Equality of retained values gives equality of whole horn maps,
    independently of compatibility witnesses and of the omitted value. *)

(** 保留值相等给出整个 horn 映射相等，与相容见证及缺失值无关。 *)

Lemma horn_faces_eq (i : Ordinal (S (S n)))
    (a c : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k, ¬ j = i → ¬ k = i → ∀ E : ¬ j = k,
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
    (K : ∀ j k, ¬ j = i → ¬ k = i → ∀ E : ¬ j = k,
      d[X; n; coface_intersection_index j k E] (c j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (c k))
    (E : ∀ j, ¬ j = i → a j ≈S c j)
  : HornFacesN i a H ≈S HornFacesN i c K.
Proof.
  apply horn_faces_unique. intros j Hj. transitivity (c j).
  - apply horn_faces_β.
  - symmetry. exact (E j Hj).
Defined.

(** Gluing the retained faces of a supplied simplex recovers its actual
    horn restriction, without selecting any filler. *)

(** 粘合给定单形的保留面恢复其实际 horn 限制，不选取任何填充。 *)

Lemma horn_faces_of_simplex (i : Ordinal (S (S n)))
    (z : X (S (S n)))
  : HornFacesN i (λ j, d[X; S n; j] z)
      (λ j k _ _ E, simplex_faces_pairwise X z j k E) ≈S
      z↾Λ[X; S (S n); i].
Proof. apply horn_faces_unique. intros j Hj. reflexivity. Defined.

(** Matching data for a complete boundary use the very same common-factor
    proof, with no chosen filler. *)

(** 完整边界的匹配数据使用同一个共同因子证明，不附带选定填充。 *)

Program Definition BoundaryFacesMatching
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k (E : ¬ j = k),
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
  : BoundaryMatchingS X (S n)
  :=
  {|matching_value j := a j
  |}.
Next Obligation.
  exact (@matching_overlap Δ (S (S n))
    (∃ j : Ordinal (S (S n)), unit) (λ _, S n)
    (λ j, δ[S n; j.1]) X
    (CofaceFacesMatching (λ _, unit) a (λ j k _ _, H j k))
    X0 (i; tt) (j; tt) f h E).
Defined.

(** Descend complete face data to an actual boundary map. *)

(** 将完整面数据下降为实际边界映射。 *)

Definition BoundaryFacesN
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k (E : ¬ j = k),
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
  : BoundaryS X (S (S n))
  := SieveMatchingN _ _ (BoundaryFacesMatching a H).

(** Every boundary face recovers its prescribed value. *)

(** 每个边界面都恢复给定值。 *)

Lemma boundary_faces_β
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k (E : ¬ j = k),
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
    (j : Ordinal (S (S n)))
  : face∂[j] (BoundaryFacesN a H) ≈S a j.
Proof. apply simplex_restrict_id. Defined.

(** A map with the prescribed complete face list is the descended boundary
    map. This is uniqueness of gluing, not uniqueness of a filler. *)

(** 具有给定完整面列表的映射等于下降所得边界映射；这是粘合的唯一性，而非
    填充的唯一性。 *)

Lemma boundary_faces_unique
    (a : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k (E : ¬ j = k),
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
    (c : BoundaryS X (S (S n)))
    (E : ∀ j, face∂[j] c ≈S a j)
  : BoundaryFacesN a H ≈S c.
Proof.
  apply (snd (boundary_map_eq_iff _ _)). intros j.
  transitivity (a j); [apply boundary_faces_β |].
  symmetry. exact (E j).
Defined.

(** Boundary descent preserves pointwise specified equality of faces;
    its compatibility witnesses need not be equal. *)

(** 边界下降保持面的逐点指定相等，无需等同相容见证。 *)

Lemma boundary_faces_eq
    (a c : Ordinal (S (S n)) → X (S n))
    (H : ∀ j k (E : ¬ j = k),
      d[X; n; coface_intersection_index j k E] (a j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (a k))
    (K : ∀ j k (E : ¬ j = k),
      d[X; n; coface_intersection_index j k E] (c j) ≈S
        d[X; n; coface_intersection_index k j
          (λ F, E (symmetry F))] (c k))
    (E : ∀ j, a j ≈S c j)
  : BoundaryFacesN a H ≈S BoundaryFacesN c K.
Proof.
  apply boundary_faces_unique. intros j. transitivity (c j).
  - apply boundary_faces_β.
  - symmetry. exact (E j).
Defined.

(** Gluing all faces of a simplex recovers its actual boundary restriction. *)

(** 粘合单形的全部面恢复其实际边界限制。 *)

Lemma boundary_faces_of_simplex (z : X (S (S n)))
  : BoundaryFacesN (λ j, d[X; S n; j] z)
      (simplex_faces_pairwise X z) ≈S z↾∂[X; S (S n)].
Proof. apply boundary_faces_unique. intros j. reflexivity. Defined.

End FaceGluing.
