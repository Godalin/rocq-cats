From Stdlib Require Import
  Arith.PeanoNat
  Lia.
From Cats.Set Require Export
  Finite.

Local Open Scope nat_scope.

(** * Operations on Finite Ordinals

    Finite positions use native equality. All map equations below are
    pointwise equations, without equality of functions or bound proofs. *)

(** * 有限序数上的运算

    有限位置使用原生相等，以下映射方程均为逐点方程，不等同函数或界证明。 *)

(** The canonical small nonempty ordinal of dimension n has n+1 positions.
    Its explicit small carrier fixes the index universe for simplex clients. *)

(** n 维规范小非空序数具有 n+1 个位置；其明确的小载体确定单纯范畴客户端的
    索引宇宙。 *)

Definition Ordinal (n : nat)
  : Set
  := Fin@{Set} (S n).

(** A rank determines its finite position. *)

(** 编号确定对应的有限位置。 *)

Lemma fin_rank_injective {n : nat} (i j : Fin n)
    (H : fin_rank i = fin_rank j)
  : i = j.
Proof.
  induction n as [|n IH] in i, j, H |- *; [destruct i |].
  destruct i as [[] | i], j as [[] | j]; cbn in H; try discriminate.
  - reflexivity.
  - f_equal. apply IH. lia.
Qed.

(** Include positions into a larger ordinal, keeping their ranks. *)

(** 将位置嵌入较大序数，并保持编号。 *)

Fixpoint fin_weaken {n : nat}
  : Fin n → Fin (S n)
  := match n as m return Fin m → Fin (S m) with
  | O => λ i, match i with end
  | S m => λ i, match i with
    | inl _ => fin_first
    | inr j => fin_next (fin_weaken j)
    end
  end.

(** Rank is unchanged by end inclusion. *)

(** 末端嵌入不改变编号。 *)

Lemma fin_weaken_rank {n : nat} (i : Fin n)
  : fin_rank (fin_weaken i) = fin_rank i.
Proof.
  induction n as [|n IH] in i |- *; [destruct i |].
  destruct i as [[] | i]; [reflexivity |].
  change (S (fin_rank (fin_weaken i)) = S (fin_rank i)).
  f_equal. apply IH.
Qed.

(** The canonical ordinal's end inclusion keeps every index. *)

(** 规范序数的末端嵌入保持每个索引。 *)

Definition ordinal_weaken {n : nat} (i : Ordinal n)
  : Ordinal (S n)
  := @fin_weaken (S n) i.

(** The canonical ordinal's successor raises every index by one. *)

(** 规范序数的后继嵌入将每个索引增加一。 *)

Definition ordinal_next {n : nat} (i : Ordinal n)
  : Ordinal (S n)
  := @fin_next (S n) i.

Declare Scope ordinal_scope.
Delimit Scope ordinal_scope with ordinal.
Bind Scope ordinal_scope with Ordinal.
Notation "i '↑'" := (ordinal_weaken i) (at level 9) : ordinal_scope.
Notation "i '⁺'" := (ordinal_next i) (at level 9) : ordinal_scope.
Local Open Scope ordinal_scope.

(** End inclusion preserves the rank of a canonical ordinal position. *)

(** 末端嵌入保持规范序数位置的编号。 *)

Lemma ordinal_weaken_rank {n : nat} (i : Ordinal n)
  : fin_rank i↑ = fin_rank i.
Proof. apply fin_weaken_rank. Qed.

(** Successor increases the rank of a canonical ordinal position. *)

(** 后继嵌入将规范序数位置的编号增加一。 *)

Lemma ordinal_next_rank {n : nat} (i : Ordinal n)
  : fin_rank i⁺ = S (fin_rank i).
Proof. reflexivity. Qed.

(** Insert a missing position at the indicated index. *)

(** 在指定索引处插入一个不在像中的位置。 *)

Fixpoint fin_skip {n : nat} (i : Fin (S n))
  : Fin n → Fin (S n).
Proof.
  destruct n as [|n]; [intros x; destruct x |].
  destruct i as [[] | i].
  - exact fin_next.
  - intros [[] | x].
    + exact fin_first.
    + exact (fin_next (@fin_skip n i x)).
Defined.

(** The inserted position is absent from the image of a skip map. *)

(** 跳过映射的像不包含所插入的位置。 *)

Lemma fin_skip_avoids {n : nat} (i : Fin (S n)) (x : Fin n)
  : ¬ fin_skip i x = i.
Proof.
  induction n as [| n IH] in i, x |- *; [destruct x |].
  destruct i as [[] | i], x as [[] | x]; cbn; try discriminate.
  intros H. apply (IH i x). now injection H.
Defined.

(** A skip map identifies no two finite positions. *)

(** 跳过映射不会等同两个不同的有限位置。 *)

Lemma fin_skip_injective {n : nat} (i : Fin (S n)) (x y : Fin n)
    (H : fin_skip i x = fin_skip i y)
  : x = y.
Proof.
  induction n as [|n IH] in i, x, y, H |- *; [destruct x |].
  destruct i as [[] | i].
  - change (fin_next x = fin_next y) in H. now injection H.
  - destruct x as [[] | x], y as [[] | y]; cbn in H;
      try discriminate; [reflexivity |].
    f_equal. apply (IH i). injection H. intros E. exact E.
Qed.

(** Every position other than the omitted one has a computational
    preimage. Only this concrete finite type uses native equality. *)

(** 除省略位置外，每个位置都有可计算原像；此处原生相等只用于具体有限类型。 *)

Fixpoint fin_unskip {n : nat} (i x : Fin (S n))
    (H : ¬ x = i)
  : ∃ y : Fin n, fin_skip i y = x.
Proof.
  destruct n as [|n].
  - destruct i as [[] | []], x as [[] | []]. destruct (H eq_refl).
  - destruct i as [[] | i], x as [[] | x].
    + destruct (H eq_refl).
    + exists x. reflexivity.
    + exists fin_first. reflexivity.
    + assert (K : ¬ x = i) by (intros E; apply H; now f_equal).
      destruct (@fin_unskip n i x K) as [y E].
      exists (fin_next y). change (fin_next (fin_skip i y) = fin_next x).
      now rewrite E.
Defined.

(** Among at least three positions one can avoid any given pair. This is
    a finite computation, not a choice principle. *)

(** 至少三个位置中总能避开任意指定的一对；这是有限计算，不使用选择原理。 *)

Definition fin_avoid_pair {n : nat} (i j : Fin (S (S (S n))))
  : ∃ k : Fin (S (S (S n))), (¬ k = i) ∧ (¬ k = j).
Proof.
  destruct i as [[] | i], j as [[] | j].
  - exists (fin_next fin_first). split; discriminate.
  - destruct j as [[] | j].
    + exists (fin_next (fin_next fin_first)). split; discriminate.
    + exists (fin_next fin_first). split; discriminate.
  - destruct i as [[] | i].
    + exists (fin_next (fin_next fin_first)). split; discriminate.
    + exists (fin_next fin_first). split; discriminate.
  - exists fin_first. split; discriminate.
Defined.

(** Among at least four positions one can avoid any three specified
    positions. The construction reduces to pair avoidance in the tail. *)

(** 至少四个位置中可避开任意三个指定位置；构造归结为尾部的成对避开。 *)

Definition fin_avoid_triple {n : nat} (i j k : Fin (S (S (S (S n)))))
  : ∃ a : Fin (S (S (S (S n)))),
      (¬ a = i) ∧ (¬ a = j) ∧ (¬ a = k).
Proof.
  destruct i as [[] | i], j as [[] | j], k as [[] | k].
  - exists (fin_next fin_first). repeat split; discriminate.
  - destruct (fin_avoid_pair k k) as [a [Ha _]].
    exists (fin_next a). repeat split; try discriminate.
    intros H. apply Ha. now injection H.
  - destruct (fin_avoid_pair j j) as [a [Ha _]].
    exists (fin_next a). repeat split; try discriminate.
    intros H. apply Ha. now injection H.
  - destruct (fin_avoid_pair j k) as [a [Hj Hk]].
    exists (fin_next a). repeat split; try discriminate;
      intros H; [apply Hj | apply Hk]; now injection H.
  - destruct (fin_avoid_pair i i) as [a [Ha _]].
    exists (fin_next a). repeat split; try discriminate.
    intros H. apply Ha. now injection H.
  - destruct (fin_avoid_pair i k) as [a [Hi Hk]].
    exists (fin_next a). repeat split; try discriminate;
      intros H; [apply Hi | apply Hk]; now injection H.
  - destruct (fin_avoid_pair i j) as [a [Hi Hj]].
    exists (fin_next a). repeat split; try discriminate;
      intros H; [apply Hi | apply Hj]; now injection H.
  - exists fin_first. repeat split; discriminate.
Defined.

(** Identify the indicated position with its immediate successor. *)

(** 将指定位置与其紧邻后继合并。 *)

Fixpoint fin_merge {n : nat} (i : Fin (S n))
  : Fin (S (S n)) → Fin (S n).
Proof.
  destruct n as [|n].
  - intros x. exact fin_first.
  - destruct i as [[] | i].
    + intros [[] | x]; [exact fin_first | exact x].
    + intros [[] | x].
      * exact fin_first.
      * exact (fin_next (@fin_merge n i x)).
Defined.

(** Natural-number rank formula for insertion. *)

(** 插入运算的自然数编号公式。 *)

Definition skip_rank (i x : nat)
  : nat
  := if x <? i then x else S x.

(** Natural-number rank formula for merging. *)

(** 合并运算的自然数编号公式。 *)

Definition merge_rank (i x : nat)
  : nat
  := if x <=? i then x else Nat.pred x.

(** Insertion commutes with successor away from the first position. *)

(** 插入在首位置之后与后继运算交换。 *)

Lemma skip_rank_succ (i x : nat)
  : skip_rank (S i) (S x) = S (skip_rank i x).
Proof.
  unfold skip_rank.
  change ((if x <? i then S x else S (S x)) =
    S (if x <? i then x else S x)).
  destruct (x <? i); reflexivity.
Qed.

(** Merging commutes with successor away from the first position. *)

(** 合并在首位置之后与后继运算交换。 *)

Lemma merge_rank_succ (i x : nat)
  : merge_rank (S i) (S x) = S (merge_rank i x).
Proof.
  unfold merge_rank. destruct x as [|x]; [reflexivity |].
  change ((if S x <=? i then S (S x) else S x) =
    S (if S x <=? i then S x else x)).
  destruct (S x <=? i); reflexivity.
Qed.

(** The structural insertion has the indicated arithmetic rank. *)

(** 结构性插入具有指定的算术编号。 *)

Lemma fin_skip_rank {n : nat} (i : Fin (S n)) (x : Fin n)
  : fin_rank (fin_skip i x) = skip_rank (fin_rank i) (fin_rank x).
Proof.
  induction n as [|n IH] in i, x |- *; [destruct x |].
  destruct i as [[] | i]; [reflexivity |].
  destruct x as [[] | x]; [reflexivity |].
  change (S (fin_rank (fin_skip i x)) =
    skip_rank (S (fin_rank i)) (S (fin_rank x))).
  rewrite IH, skip_rank_succ. reflexivity.
Qed.

(** The structural merging has the indicated arithmetic rank. *)

(** 结构性合并具有指定的算术编号。 *)

Lemma fin_merge_rank {n : nat} (i : Fin (S n)) (x : Fin (S (S n)))
  : fin_rank (fin_merge i x) = merge_rank (fin_rank i) (fin_rank x).
Proof.
  induction n as [|n IH] in i, x |- *.
  - destruct i as [[] | []], x as [[] | [[] | []]]; reflexivity.
  - destruct i as [[] | i].
    + destruct x as [[] | x]; reflexivity.
    + destruct x as [[] | x]; [reflexivity |].
      change (S (fin_rank (fin_merge i x)) =
        merge_rank (S (fin_rank i)) (S (fin_rank x))).
      rewrite IH, merge_rank_succ. reflexivity.
Qed.

(** Split decidable arithmetic comparisons in rank equations. *)

(** 在编号方程中分解可判定的算术比较。 *)

Local Ltac ordinal_arith :=
  unfold skip_rank, merge_rank in *;
  repeat match goal with
  | |- context [Nat.ltb ?x ?y] => destruct (Nat.ltb_spec0 x y)
  | |- context [Nat.leb ?x ?y] => destruct (Nat.leb_spec0 x y)
  end; lia.

(** Both arithmetic rank maps are monotone. *)

(** 两种算术编号映射均保序。 *)

Lemma skip_rank_monotone (i x y : nat) (H : x ≤ y)
  : skip_rank i x ≤ skip_rank i y.
Proof. ordinal_arith. Qed.

(** Insertion also reflects the order of positions. *)

(** 插入同样反映位置间的顺序。 *)

Lemma fin_skip_order_reflect {n : nat} (i : Fin (S n)) (x y : Fin n)
    (H : fin_rank (fin_skip i x) ≤ fin_rank (fin_skip i y))
  : fin_rank x ≤ fin_rank y.
Proof.
  rewrite !fin_skip_rank in H. unfold skip_rank in H.
  destruct (Nat.ltb_spec0 (fin_rank x) (fin_rank i));
    destruct (Nat.ltb_spec0 (fin_rank y) (fin_rank i)); lia.
Qed.

(** Merging preserves the natural-number order. *)

(** 合并保持自然数顺序。 *)

Lemma merge_rank_monotone (i x y : nat) (H : x ≤ y)
  : merge_rank i x ≤ merge_rank i y.
Proof. ordinal_arith. Qed.

(** Two insertions commute with the usual index shift. *)

(** 两次插入在通常的索引移位下交换。 *)

Lemma skip_rank_comp (i j x : nat) (H : i ≤ j)
  : skip_rank i (skip_rank j x) = skip_rank (S j) (skip_rank i x).
Proof. ordinal_arith. Qed.

(** Two mergings commute with the usual index shift. *)

(** 两次合并在通常的索引移位下交换。 *)

Lemma merge_rank_comp (i j x : nat) (H : i ≤ j)
  : merge_rank i (merge_rank (S j) x) = merge_rank j (merge_rank i x).
Proof. ordinal_arith. Qed.

(** Merging cancels insertion at its own index. *)

(** 合并消去同索引处的插入。 *)

Lemma merge_skip_rank_id (i x : nat)
  : merge_rank i (skip_rank i x) = x.
Proof. ordinal_arith. Qed.

(** Merging also cancels insertion at the following index. *)

(** 合并同样消去紧邻后继索引处的插入。 *)

Lemma merge_skip_rank_next (i x : nat)
  : merge_rank i (skip_rank (S i) x) = x.
Proof. ordinal_arith. Qed.

(** Move an insertion past a later merging. *)

(** 将插入移过其后的合并。 *)

Lemma merge_skip_rank_before (i j x : nat) (H : i ≤ j)
  : merge_rank (S j) (skip_rank i x) = skip_rank i (merge_rank j x).
Proof. ordinal_arith. Qed.

(** Move an insertion past an earlier merging. *)

(** 将插入移过其前的合并。 *)

Lemma merge_skip_rank_after (i j x : nat) (H : j < i)
  : merge_rank j (skip_rank (S i) x) = skip_rank i (merge_rank j x).
Proof. ordinal_arith. Qed.
