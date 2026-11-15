From Cats Require Export
  Instance.Set.Simplicial.Homotopy.Triangle
  Cat.Shape.Simplex.Intersection.
From Cats Require Import
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Common Time Factors from Shared Cylinder Endpoints

    Two different edges of a triangle intersect at one vertex. An
    arbitrary common time simplex, even a degenerate simplex of high
    degree, factors through that vertex. Thus agreement of cylinder maps
    at the shared endpoint gives agreement on every common time factor.
    The spatial input remains arbitrary and fixed throughout this argument.

    We reuse
    %\coqref{Cats.Cat.Shape.Simplex.Intersection.CofaceIntersectionFactor}
    {%[CofaceIntersectionFactor]%}%; there is no Kan choice or presumed
    reversal of time. The local intersection index is an omitted position:
    its zero-dimensional coface, rather than that index itself, selects
    the actual common vertex. *)

(** * 由柱的公共端点得到共同时间因子相容

    三角形的两条不同边交于一个顶点。任意共同时间单形，包括高维退化单形，
    都经过该顶点分解。因此，柱映射在公共端点上一致，就在每个共同时间因子
    上一致。整个论证中空间输入保持任意且固定。

    此处复用
    %\coqref{Cats.Cat.Shape.Simplex.Intersection.CofaceIntersectionFactor}
    {%[CofaceIntersectionFactor]%}%，不需要 Kan 选择，也不预设时间反转。
    局部交叠索引是省略位置：实际公共顶点由它的零维余面选取，而不是该索引本身。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
{[n]} \arrow[dr,dashed,"h"'] \arrow[drr,bend left=15,"t"]
  \arrow[ddr,bend right=15,"t'"'] & & \\
& {[0]} \arrow[r,"{\delta_v}"] \arrow[d,"{\delta_w}"']
  & {[1]} \arrow[d,"{\delta_j}"] \\
& {[1]} \arrow[r,"{\delta_k}"'] & {[2]}
\end{tikzcd}
\end{center}%
*)

(** The actual intersection vertex in edge j; its omitted local position
    comes from the existing coface-intersection index. *)

(** 边 j 内的实际交点；局部省略位置取自已有余面交叠索引。 *)

Definition triangle_time_overlap_vertex (j k : Ordinal 2) (E : ¬ j = k)
  : Ordinal 1%nat
  := δ[0; coface_intersection_index j k E] fin_first.

(** ** Fixed Spatial Source and Retained Time Edges

    Fix source A and target X at common ambient value bounds, with carrier
    and equality levels independent. Only retained time faces are constrained;
    their common-factor and endpoint witnesses remain Type-valued. *)

(** ** 固定空间源及保留时间边

    固定处于共同环境取值界的源 A 及目标 X，载体与相等层级独立。只约束保留
    时间面，共同因子与端点相容见证保持为 Type 值。 *)

Section TimeOverlap.
Universes u p.
Context {A X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (r : Ordinal 2).

(** The two maps agree at the actual shared endpoint, as maps from A.
    No equality between endpoint-law witnesses is requested. *)

(** 两映射作为从 A 出发的映射，在实际公共端点上一致；不要求端点定律见证相等。 *)

Definition cylinder_time_endpoint_matching
    (H : Ordinal 2 → SimplicialCylinderF A ⇒ X)
  : Type
  := ∀ j k, ¬ j = r → ¬ k = r → ∀ E : ¬ j = k,
      (H j ∘Nv SimplicialParameterPointN A (m := 1%nat)
        (triangle_time_overlap_vertex j k E)) ≈N
      (H k ∘Nv SimplicialParameterPointN A (m := 1%nat)
        (triangle_time_overlap_vertex k j (λ F, E (symmetry F)))).

(** Agreement on all common time factors keeps the same spatial simplex
    at both ends, in every degree. The omitted face remains unconstrained. *)

(** 在每维的全部共同时间因子上一致，两边保留同一空间单形；缺失面不受约束。 *)

Definition cylinder_time_factor_matching
    (H : Ordinal 2 → SimplicialCylinderF A ⇒ X)
  : Type
  := ∀ j k, ¬ j = r → ¬ k = r → ∀ n (a : A n)
      (t t' : (Δ[1]) n),
      δ[1; j] ∘ lower t ≈ δ[1; k] ∘ lower t' →
      H j n (a, t) ≈S H k n (a, t').

(** A simplex factoring through the point has constant time coordinate. *)

(** 经由点分解的单形具有常时间坐标。 *)

Local Lemma point_factor_constant n (v : Ordinal 1%nat)
    (h : (@Hom Δ) n 0%nat)
  : δ[0; v] ∘ h ≈ ConstF [Ord n] (C := [Ord 1%nat]) (δ[0; v] fin_first).
Proof.
  apply (snd (simplex_eq_iff _ _)). intros z.
  change (δ[0; v] (h z) = δ[0; v] fin_first).
  destruct (h z) as [[] | []]. reflexivity.
Defined.

(** Restrict along the computed common-vertex factor. For equal faces,
    coface injectivity gives equality of the two time inputs directly. *)

(** 沿计算所得公共顶点因子限制；面相同时，余面单射性直接给出两时间输入相等。 *)

Definition cylinder_time_factors_from_endpoints
    (H : Ordinal 2 → SimplicialCylinderF A ⇒ X)
    (EP : cylinder_time_endpoint_matching H)
  : cylinder_time_factor_matching H.
Proof.
  intros j k Hj Hk n a [t] [t'] E.
  destruct (ltac:(repeat decide equality) : {j = k} + {j <> k}) as [F | F].
  - subst k. apply func_proper. split; [reflexivity |].
    refine {|lower := _|}. apply (snd (simplex_eq_iff _ _)). intros z.
    apply (@fin_skip_injective 2 j).
    exact (fst (simplex_eq_iff _ _) E z).
  - assert (F0 : ¬ j = k) by (intros G; destruct (F G)).
    clear F. rename F0 into F.
    destruct (CofaceIntersectionFactor j k F t t' E) as [h [Ht Ht']].
    transitivity (H j n (a, {|lower := ConstF [Ord n] (C := [Ord 1%nat])
      (triangle_time_overlap_vertex j k F)|})).
    + apply func_proper. split; [reflexivity |]. refine {|lower := _|}.
      transitivity (δ[0; coface_intersection_index j k F] ∘ h).
      * symmetry. exact Ht.
      * apply point_factor_constant.
    + transitivity (H k n (a, {|lower := ConstF [Ord n] (C := [Ord 1%nat])
        (triangle_time_overlap_vertex k j (λ G, F (symmetry G)))|})).
      * exact (EP j k Hj Hk F n a).
      * apply func_proper. split; [reflexivity |]. refine {|lower := _|}.
        transitivity (δ[0; coface_intersection_index k j
          (λ G, F (symmetry G))] ∘ h).
        -- symmetry. apply point_factor_constant.
        -- exact Ht'.
Defined.

(** Constant time at the shared vertex is itself a common factor. This
    recovers endpoint agreement from the full common-factor condition. *)

(** 在公共顶点处的常时间本身就是共同因子，因此完整共同因子条件恢复端点一致。 *)

Definition cylinder_time_endpoints_from_factors
    (H : Ordinal 2 → SimplicialCylinderF A ⇒ X)
    (EF : cylinder_time_factor_matching H)
  : cylinder_time_endpoint_matching H.
Proof.
  intros j k Hj Hk E n a. apply (EF j k Hj Hk n a).
  apply (snd (simplex_eq_iff _ _)). intros z.
  change (δ[1; j] (triangle_time_overlap_vertex j k E) =
    δ[1; k] (triangle_time_overlap_vertex k j (λ F, E (symmetry F)))).
  exact (fst (simplex_eq_iff _ _) (coface_intersection_swap j k E) fin_first).
Defined.

(** These are equivalent Type-valued conditions, not equality of the
    witnesses or an equivalence instance on directed cylinder homotopies. *)

(** 两者为等价的 Type 值条件，不等同见证，也不为有向柱同伦注册等价关系实例。 *)

Definition cylinder_time_matching_iff
    (H : Ordinal 2 → SimplicialCylinderF A ⇒ X)
  : cylinder_time_endpoint_matching H ↔ cylinder_time_factor_matching H
  := (cylinder_time_factors_from_endpoints H,
      cylinder_time_endpoints_from_factors H).

(** Pointwise equal retained maps transport the common-factor condition;
    independently supplied naturality or endpoint witnesses are irrelevant. *)

(** 逐点相等的保留映射运输共同因子条件，不比较各自的自然性或端点见证。 *)

Definition cylinder_time_factor_matching_proper
    (H K : Ordinal 2 → SimplicialCylinderF A ⇒ X)
    (E : ∀ j, ¬ j = r → H j ≈N K j)
  : cylinder_time_factor_matching H ↔ cylinder_time_factor_matching K.
Proof.
  split; intros F j k Hj Hk n a t t' G.
  - transitivity (H j n (a, t)); [symmetry; apply E; exact Hj |].
    transitivity (H k n (a, t')); [exact (F j k Hj Hk n a t t' G) |].
    apply E. exact Hk.
  - transitivity (K j n (a, t)); [apply E; exact Hj |].
    transitivity (K k n (a, t')); [exact (F j k Hj Hk n a t t' G) |].
    symmetry. apply E. exact Hk.
Defined.

End TimeOverlap.
