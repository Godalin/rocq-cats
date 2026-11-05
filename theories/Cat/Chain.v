From Cats Require Export
  Cat.Shape.Ordinal.
From Cats Require Import
  Cat.Functor.Core
  Cat.Natural
  Instance.Nat.Order.

Local Open Scope nat_scope.

(** * Finite Composable Arrow Chains

    A chain stores its vertices and consecutive arrows, without storing
    composites or laws. Its ordinal interpretation composes intervals in
    the ambient category. This is the finite linear case of interpreting
    generating arrows; uniqueness uses ordinal generating-arrow naturality. *)

(** * 有限可复合箭头链

    箭头链只存储顶点和相邻箭头，不存储复合或定律。序数解释在环境范畴中复合
    区间。这是解释生成箭头的有限线性情形；唯一性复用序数生成箭头自然性。 *)

(** A chain of n arrows has n+1 vertices. Its endpoints are actual objects
    of the ambient category; no object equality is needed here. *)

(** n 条箭头的链具有 n+1 个顶点；端点是环境范畴的对象，此处不需要对象相等。 *)

Record Chain (C : Cat) (n : nat)
  :=
  { chain_vertex :> Ordinal n → @Ob C
  ; chain_edge (i : Fin@{Set} n)
    : (@Hom C) (chain_vertex (fin_weaken i)) (chain_vertex (fin_next i))
  }.

Arguments chain_edge {_ _} _ _.

(** Removing the first vertex and arrow gives the tail chain. *)

(** 删除首顶点与首箭头得到尾链。 *)

Program Definition chain_tail {C : Cat} {n : nat} (c : Chain C (S n))
  : Chain C n
  :=
  {|chain_vertex i := c (fin_next i)
  ; chain_edge i := chain_edge c (fin_next i)
  |}.

(** Evaluate an ordered interval. An empty interval is an identity, and
    a nonempty interval is folded in traversal order, later arrows on the
    left. The order witness is data in Type. *)

(** 求值有序区间：空区间为恒等，非空区间按行进顺序折叠，后走的箭头在左侧。
    顺序见证作为数据保留在 Type 中。 *)

Fixpoint chain_segment {C : Cat} {n : nat} (c : Chain C n)
    (i j : Ordinal n) (f : (@Hom [Ord n]) i j)
  : (@Hom C) (c i) (c j).
Proof.
  destruct n as [|n].
  - destruct i as [[] | []], j as [[] | []]. exact id.
  - destruct i as [[] | i], j as [[] | j].
    + exact id.
    + exact (@chain_segment C n (chain_tail c) fin_first j
        (ordinal_from_first j) ∘ chain_edge c fin_first).
    + destruct f.
    + exact (@chain_segment C n (chain_tail c) i j f).
Defined.

(** Parallel order witnesses have equal interval evaluations. *)

(** 平行顺序见证的区间求值相等。 *)

Lemma chain_segment_witness_independent {C : Cat} {n : nat}
    (c : Chain C n) (i j : Ordinal n) (f g : (@Hom [Ord n]) i j)
  : chain_segment c i j f ≈ chain_segment c i j g.
Proof.
  induction n as [|n IH] in c, i, j, f, g |- *.
  - destruct i as [[] | []], j as [[] | []]. reflexivity.
  - destruct i as [[] | i], j as [[] | j]; cbn [chain_segment].
    + reflexivity.
    + reflexivity.
    + destruct f.
    + exact (IH (chain_tail c) i j f g).
Defined.

(** Every loop interval evaluates to an identity. *)

(** 每个环区间都求值为恒等。 *)

Lemma chain_segment_id {C : Cat} {n : nat} (c : Chain C n)
    (i : Ordinal n) (f : (@Hom [Ord n]) i i)
  : chain_segment c i i f ≈ id.
Proof.
  induction n as [|n IH] in c, i, f |- *.
  - destruct i as [[] | []]. reflexivity.
  - destruct i as [[] | i]; [reflexivity |].
    exact (IH (chain_tail c) i f).
Defined.

(** A consecutive interval recovers the stored arrow. *)

(** 相邻区间恢复存储的箭头。 *)

Lemma chain_segment_step {C : Cat} {n : nat} (c : Chain C n)
    (i : Fin@{Set} n)
  : chain_segment c _ _ (ordinal_step i) ≈ chain_edge c i.
Proof.
  induction n as [|n IH] in c, i |- *; [destruct i |].
  destruct i as [[] | i].
  - change (chain_segment (chain_tail c) fin_first fin_first
      (ordinal_from_first fin_first) ∘ chain_edge c fin_first ≈
        chain_edge c fin_first).
    rewrite chain_segment_id. apply comp_id_l.
  - change (chain_segment (chain_tail c) (fin_weaken i) (fin_next i)
      (ordinal_step (fin_next i)) ≈ chain_edge (chain_tail c) i).
    transitivity (chain_segment (chain_tail c) _ _ (ordinal_step i)).
    + apply chain_segment_witness_independent.
    + exact (IH (chain_tail c) i).
Defined.

(** Splitting an interval gives the composite of its subintervals. The
    three order witnesses are arbitrary, not compared by native equality. *)

(** 分割区间得到两个子区间的复合；三个顺序见证任意，不比较其原生相等。 *)

Lemma chain_segment_comp {C : Cat} {n : nat} (c : Chain C n)
    (i j k : Ordinal n) (f : (@Hom [Ord n]) i j)
    (g : (@Hom [Ord n]) j k) (h : (@Hom [Ord n]) i k)
  : chain_segment c i k h ≈
      chain_segment c j k g ∘ chain_segment c i j f.
Proof.
  induction n as [|n IH] in c, i, j, k, f, g, h |- *.
  - destruct i as [[] | []], j as [[] | []], k as [[] | []].
    symmetry. apply comp_id_l.
  - destruct i as [[] | i], j as [[] | j], k as [[] | k];
      cbn [chain_segment].
    + symmetry. apply comp_id_l.
    + symmetry. apply comp_id_r.
    + destruct g.
    + rewrite (IH (chain_tail c) fin_first j k
        (ordinal_from_first j) g (ordinal_from_first k)).
      apply comp_assoc.
    + destruct f.
    + destruct f.
    + destruct g.
    + exact (IH (chain_tail c) i j k f g h).
Defined.

(** Interpret a chain as an ordinal diagram. All composite arrows and
    functor laws are derived from interval evaluation. *)

(** 将箭头链解释为序数图式；全部复合箭头和函子律均由区间求值导出。 *)

Program Definition ChainF {C : Cat} {n : nat} (c : Chain C n)
  : Functor [Ord n] C
  :=
  {|F0 := c
  ; F1 i j f := chain_segment c i j f
  |}.
Next Obligation.
  intros f g H. apply chain_segment_witness_independent.
Defined.
Next Obligation. apply chain_segment_id. Defined.
Next Obligation. apply chain_segment_comp. Defined.

Notation "'⟦' c '⟧Ch'" := (ChainF c) : cat_scope.

(** Extract the vertex and consecutive-arrow data of an ordinal diagram. *)

(** 提取序数图式的顶点与相邻箭头数据。 *)

Program Definition diagram_chain {C : Cat} {n : nat}
    (F : Functor [Ord n] C)
  : Chain C n
  :=
  {|chain_vertex := F
  ; chain_edge i := fmap F (ordinal_step i)
  |}.

Notation "'⌊' F '⌋Ch'" := (diagram_chain F) : cat_scope.

(** Extracting an interpreted chain recovers every stored arrow. *)

(** 提取已解释的箭头链恢复每条存储箭头。 *)

Lemma chain_diagram_β {C : Cat} {n : nat} (c : Chain C n)
    (i : Fin@{Set} n)
  : chain_edge ⌊⟦c⟧Ch⌋Ch i ≈ chain_edge c i.
Proof. exact (chain_segment_step c i). Defined.

(** Prescribed components define a comparison out of the interpreted chain
    exactly when their squares commute on its generating arrows. *)

(** 指定分量在生成箭头上的方块交换时，给出从箭头链解释出发的自然比较。 *)

Program Definition ChainCompareN {C : Cat} {n : nat} (c : Chain C n)
    (F : Functor [Ord n] C) (α : ∀ i, Hom (c i) (F i))
    (H : ∀ i, α (fin_next i) ∘ chain_edge c i ≈
      fmap F (ordinal_step i) ∘ α (fin_weaken i))
  : ⟦c⟧Ch ⇒ F
  :=
  {|nt := α
  |}.
Next Obligation.
  refine (ordinal_naturality_steps ⟦c⟧Ch F α _ X Y f). intros i.
  change (α (fin_next i) ∘ chain_segment c _ _ (ordinal_step i) ≈
    fmap F (ordinal_step i) ∘ α (fin_weaken i)).
  rewrite chain_segment_step. apply H.
Defined.

(** Reconstructing an ordinal diagram from its chain gives an
    identity-component natural isomorphism, not equality of functor records. *)

(** 从箭头链重构序数图式得到恒等分量的自然同构，不要求函子记录相等。 *)

Definition chain_diagram_η {C : Cat} {n : nat}
    (F : Functor [Ord n] C)
  : ⟦⌊F⌋Ch⟧Ch ≅N F.
Proof.
  unshelve refine ((ChainCompareN ⌊F⌋Ch F (λ i, id) _); _).
  - intros i. cbn. rewrite comp_id_l, comp_id_r. reflexivity.
  - intros i. exists id. split; apply comp_id_l.
Defined.

(** Substitute an ordinal map in a chain by interpreting its image
    intervals and extracting consecutive arrows again. *)

(** 通过解释像区间并再次提取相邻箭头，沿序数映射替换箭头链。 *)

Definition chain_reindex {C : Cat} {m n : nat}
    (Q : Functor [Ord m] [Ord n]) (c : Chain C n)
  : Chain C m
  := ⌊⟦c⟧Ch ∘F Q⌋Ch.

Notation "c '[' Q ']Ch'" := (chain_reindex Q c)
  (at level 8, left associativity, format "c [ Q ]Ch") : cat_scope.
