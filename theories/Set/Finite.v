From Cats.Set Require Export Core.

(** * Finite Positions

    The empty type and repeated finite sums give n positions without
    arithmetic bounds or proof fields. This concrete set uses native equality. *)

(** * 有限位置

    空类型及重复有限和给出 n 个位置，不携带算术界或证明字段；这个具体集合使用
    原生相等。 *)

Fixpoint Fin (n : nat)
  : Type
  := match n with O => Empty_set | S n => unit + Fin n end.

(** The first position in a nonempty finite type. *)

(** 非空有限类型的首位置。 *)

Definition fin_first {n : nat}
  : Fin (S n)
  := inl tt.
(** Include a position after the first position. *)

(** 将位置嵌入首位置之后。 *)

Definition fin_next {n : nat} (i : Fin n)
  : Fin (S n)
  := inr i.

(** The zero-based natural-number rank of a finite position. *)

(** 有限位置从零起算的自然数编号。 *)

Fixpoint fin_rank {n : nat}
  : Fin n → nat
  := match n as m return Fin m → nat with
  | O => λ i, match i with end
  | S m => λ i, match i with inl _ => O | inr j => S (@fin_rank m j) end
  end.

(** Finite positions with native equality as their specified setoid equality. *)

(** 以原生相等作为指定相等的有限位置广集。 *)

Program Definition FinS@{u p +} (n : nat)
  : SetC@{u p}
  :=
  {|carrier := Fin n
  ; carrier_equiv x y := (x = y : Type@{p})
  |}.
Next Obligation.
  split.
  - intros x. reflexivity.
  - intros x y H. symmetry. exact H.
  - intros x y z H K. transitivity y; assumption.
Defined.
