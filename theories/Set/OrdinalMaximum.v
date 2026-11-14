From Cats.Set Require Export
  Ordinal.
From Stdlib Require Import
  Arith.PeanoNat
  Lia.

Local Open Scope nat_scope.

(** * Computable Maxima of Finite Ordinal Families

    Select actual finite positions rather than bounded natural numbers
    with proof fields. The empty family has maximum zero; a nonempty
    family is folded with a binary maximum. This construction only uses
    the native equality and order of concrete finite positions. A geometric
    client is the computable staircase pivot in
    %\coqref{Cats.Cat.Shape.Simplex.Prism.simplex_prism_pivot}
    {%[simplex_prism_pivot]%}%. *)

(** * 有限序数族的可计算最大值

    直接选择实际有限位置，不使用附带界证明的自然数。空族最大值取零，非空族
    用二元最大值折叠。构造只用具体有限位置的原生相等和顺序。一个几何客户端是
    %\coqref{Cats.Cat.Shape.Simplex.Prism.simplex_prism_pivot}
    {%[simplex_prism_pivot]%}% 中可计算的阶梯枢轴。 *)

(** Choose the larger position, choosing the second on a tie. *)

(** 选择较大位置，编号相同时选择第二项。 *)

Definition ordinal_max {m : nat} (i j : Ordinal m)
  : Ordinal m
  := if Nat.leb (fin_rank i) (fin_rank j) then j else i.

(** The selected position has the arithmetic maximum rank. *)

(** 所选位置的编号为算术最大值。 *)

Lemma ordinal_max_rank {m : nat} (i j : Ordinal m)
  : fin_rank (ordinal_max i j) = Nat.max (fin_rank i) (fin_rank j).
Proof.
  unfold ordinal_max. destruct (Nat.leb_spec0 (fin_rank i) (fin_rank j)).
  - symmetry. apply Nat.max_r. assumption.
  - symmetry. apply Nat.max_l. lia.
Defined.

(** The finite fold has a zero default and retains actual positions. *)

(** 有限折叠以零为默认值，保留实际位置。 *)

Fixpoint finite_ordinal_max {m : nat} (n : nat)
    (f : Fin@{Set} n → Ordinal m)
  : Ordinal m
  := match n as k return (Fin@{Set} k → Ordinal m) → Ordinal m with
  | O => λ _, fin_first
  | S k => λ g, ordinal_max (g fin_first)
      (finite_ordinal_max k (λ i, g (fin_next i)))
  end f.

(** Every family member is at most the selected maximum. *)

(** 每个族成员都不超过所选最大值。 *)

Lemma finite_ordinal_max_upper {m n : nat} (f : Fin@{Set} n → Ordinal m)
    (i : Fin@{Set} n)
  : fin_rank (f i) ≤ fin_rank (finite_ordinal_max n f).
Proof.
  induction n as [|n IH] in f, i |- *; [destruct i |].
  cbn [finite_ordinal_max]. rewrite ordinal_max_rank.
  destruct i as [[] | i].
  - apply Nat.le_max_l.
  - transitivity (fin_rank (finite_ordinal_max n (λ j, f (fin_next j)))).
    + exact (IH (λ j, f (fin_next j)) i).
    + apply Nat.le_max_r.
Defined.

(** Every common upper bound also bounds the selected maximum. *)

(** 每个共同上界也约束所选最大值。 *)

Lemma finite_ordinal_max_bound {m n : nat} (f : Fin@{Set} n → Ordinal m)
    (r : nat) (H : ∀ i, fin_rank (f i) ≤ r)
  : fin_rank (finite_ordinal_max n f) ≤ r.
Proof.
  induction n as [|n IH] in f, H |- *; [cbn; lia |].
  cbn [finite_ordinal_max]. rewrite ordinal_max_rank.
  apply Nat.max_lub.
  - apply H.
  - apply IH. intros i. apply H.
Defined.

(** Pointwise equality of finite families preserves their selected value;
    no equality of functions or arithmetic proof fields is used. *)

(** 有限族逐点相等保持所选值，不使用函数或算术证明字段的相等。 *)

Lemma finite_ordinal_max_proper {m n : nat}
    (f g : Fin@{Set} n → Ordinal m) (H : ∀ i, f i = g i)
  : finite_ordinal_max n f = finite_ordinal_max n g.
Proof.
  induction n as [|n IH] in f, g, H |- *; [reflexivity |].
  cbn [finite_ordinal_max]. rewrite (H fin_first).
  f_equal. apply IH. intros i. apply H.
Defined.
