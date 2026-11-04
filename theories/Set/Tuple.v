From Cats.Set Require Export
  Finite
  Morphism.

Local Open Scope nat_scope.

(** * Finite Tuples with Pointwise Equality

    Constructors act on carriers; their respectfulness laws are given below.
    Write [X ^S n], [[]S] and [x ∷S xs] for tuple setoids, empty tuples and
    prepending, respectively. *)

(** * 带逐项相等的有限元组

    构造器作用于载体，其保相等定律在下方给出。元组广集、空元组及前添操作分别
    记作 [X ^S n]、[[]S] 和 [x ∷S xs]。 *)

(** A tuple has n entries indexed by the canonical small finite positions.
    Its equality uses only the specified equality of the entries. *)

(** 元组具有由规范小有限位置索引的 n 个分量；其相等只使用分量的指定相等。 *)

Program Definition TupleS@{u p +} (X : SetC@{u p}) (n : nat)
  : SetC@{u p}
  :=
  {|carrier := Fin@{Set} n → X
  ; carrier_equiv x y := ∀ i, x i ≈S y i
  |}.
Next Obligation.
  split.
  - intros x i. reflexivity.
  - intros x y H i. symmetry. exact (H i).
  - intros x y z H K i. transitivity (y i); [exact (H i) | exact (K i)].
Defined.

Notation "X '^S' n" := (TupleS X n)
  (at level 30, right associativity) : set_scope.

(** The empty tuple is the function with empty domain. *)

(** 空元组是定义域为空的函数。 *)

Definition tuple_nil {A : Type}
  : Fin@{Set} 0 → A
  := λ i, match i with end.

Notation "'[]S'" := tuple_nil : set_scope.

(** Prepend an entry to a finite tuple. *)

(** 向有限元组前方添加一个分量。 *)

Definition tuple_cons {A : Type} {n : nat}
    (x : A) (xs : Fin@{Set} n → A)
  : Fin@{Set} (S n) → A
  := λ i, match i with inl _ => x | inr j => xs j end.

Notation "x '∷S' xs" := (tuple_cons x xs)
  (at level 60, right associativity) : set_scope.

(** The first entry of a nonempty tuple. *)

(** 非空元组的首分量。 *)

Definition tuple_head {A : Type} {n : nat} (xs : Fin@{Set} (S n) → A)
  : A
  := xs fin_first.

(** Remove the first entry of a nonempty tuple. *)

(** 移除非空元组的首分量。 *)

Definition tuple_tail {A : Type} {n : nat} (xs : Fin@{Set} (S n) → A)
  : Fin@{Set} n → A
  := λ i, xs (fin_next i).

(** Prepending preserves equality of both the entry and the tail. *)

(** 前添操作保持首分量和尾元组的相等。 *)

Global Instance tuple_cons_proper {X : SetC} {n : nat}
  : Proper (carrier_equiv X ==> carrier_equiv (X ^S n) ==>
      carrier_equiv (X ^S S n)) (@tuple_cons X n).
Proof. intros x y H xs ys K [[] | i]; [exact H | exact (K i)]. Defined.

(** Taking the head preserves equality. *)

(** 取首分量保持相等。 *)

Global Instance tuple_head_proper {X : SetC} {n : nat}
  : Proper (carrier_equiv (X ^S S n) ==> carrier_equiv X)
      (@tuple_head X n).
Proof. intros x y H. exact (H fin_first). Defined.

(** Taking the tail preserves equality. *)

(** 取尾元组保持相等。 *)

Global Instance tuple_tail_proper {X : SetC} {n : nat}
  : Proper (carrier_equiv (X ^S S n) ==> carrier_equiv (X ^S n))
      (@tuple_tail X n).
Proof. intros x y H i. exact (H (fin_next i)). Defined.

(** Head and tail reconstruct every nonempty tuple up to its specified
    equality, without equality of functions. *)

(** 首分量和尾元组按指定相等重构每个非空元组，不要求函数相等。 *)

Lemma tuple_η {X : SetC} {n : nat} (xs : X ^S S n)
  : (tuple_head xs ∷S tuple_tail xs : X ^S S n) ≈S xs.
Proof. intros [[] | i]; reflexivity. Defined.
