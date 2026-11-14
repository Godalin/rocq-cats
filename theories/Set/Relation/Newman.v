From Cats.Set.Relation Require Export
  Confluence
  StrongNormalization.

(** * Newman's Lemma with Computational Joins

    Local confluence only resolves peaks of two steps. A strongly
    normalizing tree makes it possible to iterate these resolutions and
    join arbitrary finite paths. The construction recurses on that tree,
    retaining the common reduct and both paths at every stage.

    In particular, the proof does not choose a normalization strategy or
    derive termination from the absence of infinite sequences. The input
    tree and the output paths have independent universe bounds. *)

(** * 带计算性汇合见证的 Newman 引理

    局部合流只解决两个单步的分叉。强归一化树允许迭代这些局部解法，汇合
    任意有限路径。构造对该树递归，在每一阶段保留共同归约结果及两条路径。

    证明不选择归一化策略，也不从不存在无限序列推导终止性。输入树和输出
    路径具有独立的宇宙界。 *)

Local Open Scope relation_scope.

(** ** From Local to Global Peaks

    Fix a Type-valued relation and a local joining operation. At a root
    with a normalization tree, recursive calls resolve peaks below its
    immediate successors. The local join may take several steps on each
    side, so confluence must also be inherited along these finite paths. *)

(** ** 从局部分叉到一般分叉

    固定 Type 值关系及局部汇合操作。在具有归一化树的根处，递归调用处理
    直接后继以下的分叉。局部汇合的每一侧可能包含多步，因此还需沿这些有限
    路径继承合流性。 *)

Section Newman.
Universes a r p s.
Context {A : Type@{a}} {R : A → A → Type@{r}}.
Context (local : is_locally_confluent@{a r p _} R).

(** Strong normalization is needed only at the chosen source. For a
    nonempty peak, first join its initial steps, then use confluence below
    them to join the tails and finally their common descendants. *)

(** 只要求选定来源强归一化。对于非空分叉，先汇合首步，再用其下方的合流性
    汇合尾部，最后汇合得到的共同后继。 *)

Definition newman_at {x : A} (normal : SN@{a r s} R x)
  : is_confluent_at@{a r p _} R x.
Proof.
  induction normal as [x next ih]. intros y z left right.
  destruct left as [x | x a y h tail].
  - exists z. exact (right, rtc_refl z).
  - destruct right as [x | x b z k tail'].
    + exists y. exact (rtc_refl y, rtc_cons h tail).
    + destruct (local x a b h k) as [u [p q]].
      destruct (ih a h y u tail p) as [v [yv uv]].
      destruct (ih b k z u tail' q) as [w [zw uw]].
      destruct (confluent_at_descendant (ih a h) p v w uv uw)
        as [c [vc wc]].
      exists c. exact (rtc_trans yv vc, rtc_trans zw wc).
Defined.

(** A tree at every source gives confluence everywhere. The conclusion
    supplies joins, not merely a proposition asserting their existence. *)

(** 每个来源处的树给出全局合流。结论提供汇合见证，而非只断言它们存在的命题。 *)

Definition newman (normal : ∀ x, SN@{a r s} R x)
  : is_confluent@{a r p _} R
  := λ x, newman_at (normal x).

End Newman.
