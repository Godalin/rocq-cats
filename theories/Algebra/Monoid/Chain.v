From Cats Require Export
  Algebra.Monoid.Core.
From Cats.Set Require Export
  Tuple
  Ordinal.
From Stdlib Require Import
  Arith.PeanoNat
  Lia.

Local Open Scope nat_scope.
Local Open Scope monoid_scope.

(** * Products of Consecutive Arrows in a Monoid

    A tuple lists arrows in traversal order. A later arrow multiplies on
    the left, consistently with the single-object category convention.
    Write [xs⟦i, j⟧⋅] for a segment product and [xs[f]M] for substitution. *)

(** * 幺半群中连续箭头的积

    元组按行进顺序列出箭头；后走的箭头乘在左侧，与单对象范畴的约定一致。
    段积记作 [xs⟦i, j⟧⋅]，替换记作 [xs[f]M]。 *)

Section Chain.
Context {M : SetC} `{HM : !Monoid M}.

(** The product of the half-open arrow segment from vertex i to vertex j.
    Unordered endpoints return the unit; laws only use ordered endpoints. *)

(** 从顶点 i 到顶点 j 的半开箭头段之积。逆序端点返回单位元；定律只使用有序
    端点。 *)

Fixpoint monoid_segment {n : nat} (xs : M ^S n) (i j : Ordinal n)
  : M.
Proof.
  destruct n as [|n]; [exact 1 |].
  destruct i as [[] | i], j as [[] | j].
  - exact 1.
  - exact (@monoid_segment n (tuple_tail xs) fin_first j ⋅ tuple_head xs).
  - exact 1.
  - exact (@monoid_segment n (tuple_tail xs) i j).
Defined.

(** Segment products preserve equality of the tuple and of finite endpoints. *)

(** 段积保持元组相等及有限端点相等。 *)

Global Instance monoid_segment_proper {n : nat}
  : Proper (carrier_equiv (M ^S n) ==> eq ==> eq ==> carrier_equiv M)
      (@monoid_segment n).
Proof.
  intros xs ys H i i' Hi j j' Hj. subst i' j'.
  induction n as [|n IH] in xs, ys, H, i, j |- *.
  - reflexivity.
  - destruct i as [[] | i], j as [[] | j]; cbn [monoid_segment].
    + reflexivity.
    + apply magma_mul_proper.
      * apply IH. apply tuple_tail_proper. exact H.
      * exact (H fin_first).
    + reflexivity.
    + apply IH. apply tuple_tail_proper. exact H.
Defined.

(** An empty segment has unit product. *)

(** 空段的积是单位元。 *)

Lemma monoid_segment_id {n : nat} (xs : M ^S n) (i : Ordinal n)
  : monoid_segment xs i i ≈S 1.
Proof.
  induction n as [|n IH] in xs, i |- *; [reflexivity |].
  destruct i as [[] | i]; [reflexivity | apply IH].
Defined.

(** The segment between consecutive vertices recovers the corresponding
    tuple entry. *)

(** 相邻顶点之间的段恢复对应的元组分量。 *)

Lemma monoid_segment_step {n : nat} (xs : M ^S n)
    (i : Fin@{Set} n)
  : monoid_segment xs (fin_weaken i) (fin_next i) ≈S xs i.
Proof.
  induction n as [|n IH] in xs, i |- *; [destruct i |].
  destruct i as [[] | i].
  - change (monoid_segment (tuple_tail xs) fin_first fin_first ⋅
      tuple_head xs ≈S tuple_head xs).
    rewrite monoid_segment_id. apply monoid_unit_l.
  - apply IH.
Defined.

(** Splitting an ordered segment gives the product of the two subsegments. *)

(** 分割有序段得到两个子段之积。 *)

Lemma monoid_segment_comp {n : nat} (xs : M ^S n)
    (i j k : Ordinal n)
    (Hij : fin_rank i ≤ fin_rank j) (Hjk : fin_rank j ≤ fin_rank k)
  : monoid_segment xs i k ≈S
      monoid_segment xs j k ⋅ monoid_segment xs i j.
Proof.
  induction n as [|n IH] in xs, i, j, k, Hij, Hjk |- *.
  - symmetry. apply monoid_unit_l.
  - destruct i as [[] | i], j as [[] | j], k as [[] | k];
      cbn [fin_rank] in Hij, Hjk; try lia;
      cbn [monoid_segment].
    + symmetry. apply monoid_unit_l.
    + symmetry. apply monoid_unit_r.
    + rewrite (IH (tuple_tail xs) fin_first j k).
      * apply semigroup_assoc.
      * cbn. lia.
      * cbn. lia.
    + apply IH; cbn in *; lia.
Defined.

(** A vertex map acts on an arrow chain by multiplying its image segments.
    Monotonicity is needed for the laws, not for this computational map. *)

(** 顶点映射通过对像中的各段取积作用于箭头链；保序性用于定律，不用于此计算
    映射的定义。 *)

Definition monoid_chain_sub {m n : nat}
    (f : Ordinal m → Ordinal n) (xs : M ^S n)
  : M ^S m
  := λ i, monoid_segment xs (f (fin_weaken i)) (f (fin_next i)).

(** Substitution preserves equality of the chain. *)

(** 替换保持箭头链相等。 *)

Global Instance monoid_chain_sub_proper {m n : nat}
    (f : Ordinal m → Ordinal n)
  : Proper (carrier_equiv (M ^S n) ==> carrier_equiv (M ^S m))
      (monoid_chain_sub f).
Proof.
  intros xs ys H i. apply monoid_segment_proper;
    [exact H | reflexivity | reflexivity].
Defined.

(** Equal finite vertex maps give equal substituted chains. *)

(** 相等的有限顶点映射给出相等的替换箭头链。 *)

Lemma monoid_chain_sub_map {m n : nat}
    (f g : Ordinal m → Ordinal n) (H : ∀ i, f i = g i) (xs : M ^S n)
  : monoid_chain_sub f xs ≈S monoid_chain_sub g xs.
Proof. intros i. unfold monoid_chain_sub. rewrite !H. reflexivity. Defined.

(** Substitution along the identity preserves each entry. *)

(** 沿恒等的替换保持各分量。 *)

Lemma monoid_chain_sub_id {n : nat} (xs : M ^S n)
  : monoid_chain_sub (λ i, i) xs ≈S xs.
Proof. intros i. apply monoid_segment_step. Defined.

(** The product of a substituted segment is the original product between
    its endpoint images. This is the key subdivision law. *)

(** 替换后段的积是原箭头链中两个端点的像之间的积；这是关键的细分定律。 *)

Lemma monoid_segment_sub {m n : nat}
    (f : Ordinal m → Ordinal n)
    (Hf : ∀ i j, fin_rank i ≤ fin_rank j → fin_rank (f i) ≤ fin_rank (f j))
    (xs : M ^S n) (i j : Ordinal m) (Hij : fin_rank i ≤ fin_rank j)
  : monoid_segment (monoid_chain_sub f xs) i j ≈S
      monoid_segment xs (f i) (f j).
Proof.
  induction m as [|m IH] in f, Hf, i, j, Hij |- *.
  - destruct i as [[] | []], j as [[] | []].
    symmetry. apply monoid_segment_id.
  - destruct i as [[] | i], j as [[] | j]; cbn [fin_rank] in Hij;
      try lia; cbn [monoid_segment].
    + symmetry. apply monoid_segment_id.
    + change (monoid_segment
        (monoid_chain_sub (λ k, f (fin_next k)) xs) fin_first j ⋅
        monoid_segment xs (f fin_first) (f (fin_next fin_first)) ≈S
        monoid_segment xs (f fin_first) (f (fin_next j))).
      assert (Htail : ∀ a b : Ordinal m, fin_rank a ≤ fin_rank b →
        fin_rank (f (fin_next a)) ≤ fin_rank (f (fin_next b))).
      { intros a b H. apply Hf. cbn in *. lia. }
      rewrite (IH (λ k, f (fin_next k)) Htail fin_first j
        (Nat.le_0_l _)).
      symmetry. apply monoid_segment_comp; apply Hf; cbn in *; lia.
    + apply (IH (λ k, f (fin_next k))).
      * intros a b H. apply Hf. cbn in *. lia.
      * cbn in *. lia.
Defined.

(** Monotone substitutions compose by composing their vertex maps. *)

(** 保序替换通过复合顶点映射来复合。 *)

Lemma monoid_chain_sub_comp {l m n : nat}
    (f : Ordinal m → Ordinal n) (g : Ordinal l → Ordinal m)
    (Hf : ∀ i j, fin_rank i ≤ fin_rank j → fin_rank (f i) ≤ fin_rank (f j))
    (Hg : ∀ i j, fin_rank i ≤ fin_rank j → fin_rank (g i) ≤ fin_rank (g j))
    (xs : M ^S n)
  : monoid_chain_sub g (monoid_chain_sub f xs) ≈S
      monoid_chain_sub (λ i, f (g i)) xs.
Proof.
  intros i. change (monoid_segment (monoid_chain_sub f xs)
    (g (fin_weaken i)) (g (fin_next i)) ≈S
    monoid_segment xs (f (g (fin_weaken i))) (f (g (fin_next i)))).
  apply (monoid_segment_sub f Hf).
  apply Hg. rewrite fin_weaken_rank. cbn. lia.
Defined.

End Chain.

Notation "xs '⟦' i ',' j '⟧⋅'" := (monoid_segment xs i j)
  (at level 8, left associativity, format "xs ⟦ i , j ⟧⋅") : monoid_scope.
Notation "xs '[' f ']M'" := (monoid_chain_sub f xs)
  (at level 8, left associativity, format "xs [ f ]M") : monoid_scope.
