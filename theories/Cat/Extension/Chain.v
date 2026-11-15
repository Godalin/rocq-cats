From Cats Require Export
  Cat.Extension.Core
  Cat.Chain.
From Cats Require Import
  Cat.Core.

(** * Extending Maps Along Finite Chains

    [Chain] already retains vertices and adjacent arrows, and
    [chain_segment] already composes each ordered interval. Here one
    supplied extension operation for each edge gives extension operations
    for all those intervals. The recursion follows the same traversal as
    [chain_segment], reusing [map_extension_target_id] and
    [map_extension_target_comp]. No second notion of chain or composite
    is needed.

    Each operation returns an actual map and its restriction equation.
    Only traversed edges are evaluated. The supplied choices need not
    be respectful or unique; changing choices is not asserted to give
    equal extensions. *)

(** * 沿有限链延拓映射

    [Chain] 已保留顶点和相邻箭头，[chain_segment] 已复合每个有序区间。
    此处为每条边给定一个延拓操作，就得到全部区间的延拓操作。递归沿同一顺序
    行进，复用 [map_extension_target_id] 和 [map_extension_target_comp]，
    不另定义链或复合。

    每个操作返回实际映射及其限制方程，只求值经过的边。给定选择不必保相等或
    唯一；不声称改变选择后得到的延拓相等。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
A_i \arrow[r] \arrow[dr,"a"'] & \cdots \arrow[r]
  & A_j \arrow[dl,dashed,"b"] \\
& Q
\end{tikzcd}
\qquad $b\circ\operatorname{segment}_{i,j}\approx a.$
\end{center}%
*)

(** ** An Arbitrary Ambient Category

    Fix a category with its specified Hom equality. Its arrow and
    equality-witness sizes remain independent. For a supplied finite
    chain and target, require extensions only along its actual edges;
    no chosen colimits, filler structure or global model is selected. *)

(** ** 任意环境范畴

    固定具有指定 Hom 相等的范畴，保持箭头与相等见证大小独立。给定有限链和
    目标，只要求沿其实际边的延拓，不选择余极限、填充结构或全局模型。 *)

Section ChainExtensions.
Context {C : Cat}.

(** Every ordered segment admits the transparent successive extension.
    The empty segment uses the original map. A segment leaving the first
    vertex extends across the first edge and then the tail segment;
    other nonempty segments use only the tail's edge choices. *)

(** 每个有序区间都有透明的逐次延拓。空区间使用原映射；离开首顶点的区间先跨
    首边延拓，再跨尾链区间延拓，其他非空区间只使用尾链的边选择。 *)

Fixpoint chain_extension_target {n : nat} (c : Chain C n) (Q : @Ob C)
    (E : ∀ k, is_extension_target (chain_edge c k) Q)
    (i j : Ordinal n) (f : (@Hom [Ord n]) i j)
  : is_extension_target (chain_segment c i j f) Q.
Proof.
  destruct n as [|n].
  - destruct i as [[] | []], j as [[] | []].
    exact (map_extension_target_id (c fin_first) Q).
  - destruct i as [[] | i], j as [[] | j].
    + exact (map_extension_target_id (c fin_first) Q).
    + exact (map_extension_target_comp (chain_edge c fin_first)
        (chain_segment (chain_tail c) fin_first j (ordinal_from_first j))
        (E fin_first)
        (@chain_extension_target n (chain_tail c) Q
          (λ k, E (fin_next k)) fin_first j (ordinal_from_first j))).
    + destruct f.
    + exact (@chain_extension_target n (chain_tail c) Q
        (λ k, E (fin_next k)) i j f).
Defined.

End ChainExtensions.
