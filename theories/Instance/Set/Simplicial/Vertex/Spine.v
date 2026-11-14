From Cats Require Export
  Instance.Set.Vertex.Chain
  Instance.Set.Simplicial.Vertex.Core.
From Cats Require Import
  Instance.Set.Lift.

Local Open Scope nat_scope.

(** * Reconstructing Simplices from Their Spines

    A spine records vertices and consecutive arrows. The vertex nerve is
    degreewise isomorphic to these chain setoids, with the same specified
    vertex transport in the equality. Both sides are raised explicitly to
    common value sizes, without identifying their native universe levels. *)

(** * 从脊重构单形

    脊记录顶点及相邻箭头。顶点 nerve 与这些箭头链广集逐维同构，相等中使用同一
    指定顶点运输。两侧显式提升至共同值大小，不等同各自的原生宇宙层级。 *)

(** ** Why the Consecutive Edges Suffice Here

    In the preceding nerve triangle, the long edge was forced to be the
    composite. The same idea works in every dimension: a chain of n arrows
    determines every longer edge by composition. %\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.spine resp}
    {%[spine_resp]%}% reads the
    consecutive arrows, and %\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.spine inv resp}
    {%[spine_inv_resp]%}% restores the whole ordinal
    diagram. %\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.spine xCExB2}
    {%[spine_β]%}% and %\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.spine xCExB7}
    {%[spine_η]%}% state the two inverse laws.

    This is a theorem about this nerve, not about arbitrary simplicial sets.
    In general, specifying the consecutive edges need not determine a
    simplex or even guarantee one exists. The later horn chapters study
    precisely such extension questions. *)

(** ** 为什么这里的相邻边已经足够

    前面的 nerve 三角形中，长边必须等于复合。各维都采用同样的思想：n 条
    箭头组成的链通过复合确定每条更长的边。%\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.spine resp}
    {%[spine_resp]%}% 读出相邻箭头，
    %\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.spine inv resp}
    {%[spine_inv_resp]%}% 恢复整个序数图式，%\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.spine xCExB2}
    {%[spine_β]%}% 和 %\coqref{Cats.Instance.Set.Simplicial.Vertex.Spine.spine xCExB7}
    {%[spine_η]%}% 给出两条
    互逆律。

    这是关于这个 nerve 的定理，不是任意单纯集合的性质。一般而言，指定相邻边
    未必确定一个单形，甚至不能保证存在单形。后面的 horn 章节研究的正是这种
    延拓问题。 *)

(** Extract the spine of a simplex, preserving its specified equality. *)

(** 提取单形的脊，并保持其指定相等。 *)

Definition spine_resp@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {n : nat}
  : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n →r
      LiftS (VertexChainS T n)
  := (vertex_chain_resp T n)^↑S.

(** Reconstruct a simplex by composing the intervals of its spine. *)

(** 通过复合脊的区间重构单形。 *)

Definition spine_inv_resp@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {n : nat}
  : LiftS (VertexChainS T n) →r
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n
  := (vertex_chain_diagram_resp T n)^↑S.

Notation "'⌊' x '⌋Sp[' T ';' n ']'" := (@spine_resp _ _ T n x)
  : hom_scope.
Notation "'⟦' c '⟧Sp[' T ';' n ']'" := (@spine_inv_resp _ _ T n c)
  : hom_scope.

(** Extracting the reconstructed simplex recovers its chain. *)

(** 提取重构的单形恢复其箭头链。 *)

Lemma spine_β@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {n : nat}
    (c : LiftS@{_ _ u p} (VertexChainS T n))
  : ⌊⟦c⟧Sp[T; n]⌋Sp[T; n] ≈S c.
Proof.
  destruct c as [c]. exact {|lower := vertex_chain_β T c
                           |}.
Defined.

(** Reconstructing the extracted spine recovers its simplex. *)

(** 重构提取的脊恢复其单形。 *)

Lemma spine_η@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {n : nat}
    (x : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : ⟦⌊x⌋Sp[T; n]⟧Sp[T; n] ≈S x.
Proof.
  destruct x as [F]. exact {|lower := vertex_chain_η T F
                           |}.
Defined.

(** The spine correspondence is an isomorphism of the specified setoids.
    Reconstruction and both inverse laws retain their computation. *)

(** 脊对应是指定广集的同构；重构及两条互逆律均保留计算行为。 *)

Definition vertex_spine_iso@{u p +} {X : SetC} {C : Cat}
    (T : Functor (EqGpd X) C) (n : nat)
  : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n ≅[SetCat]
      LiftS (VertexChainS T n).
Proof.
  exists spine_resp, spine_inv_resp. split.
  - intros x. exact (spine_η x).
  - intros c. exact (spine_β c).
Defined.

(** Simplices are equal exactly when their spines are equal. *)

(** 单形相等当且仅当其脊相等。 *)

Lemma spine_eq_iff@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {n : nat}
    (x y : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : x ≈S y ↔ ⌊x⌋Sp[T; n] ≈S ⌊y⌋Sp[T; n].
Proof.
  split.
  - intros H. exact (@func_proper _ _ spine_resp x y H).
  - intros H. transitivity ⟦⌊x⌋Sp[T; n]⟧Sp[T; n].
    + symmetry. apply spine_η.
    + transitivity ⟦⌊y⌋Sp[T; n]⟧Sp[T; n].
      * exact (@func_proper _ _ spine_inv_resp _ _ H).
      * apply spine_η.
Defined.

(** Restriction of a simplex corresponds to interval substitution in its
    spine, including faces and degeneracies. *)

(** 单形限制对应于脊中的区间替换，特别包括面与退化。 *)

Lemma spine_restrict@{u p +} {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C} {m n : nat} (θ : (@Hom Δ) m n)
    (x : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
  : ⌊Nᵥ(T)[θ]Δ x⌋Sp[T; m] ≈S
      (vertex_chain_reindex_resp T θ)^↑S ⌊x⌋Sp[T; n].
Proof.
  destruct x as [F]. refine {|lower := _
                            |}.
  apply (@func_proper _ _ (vertex_chain_resp T m)).
  apply (@func_proper _ _ (vertex_diagram_precomp_resp T θ)).
  symmetry. exact (vertex_chain_η T F).
Defined.
