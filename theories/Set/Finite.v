From Cats.Set Require Export Core.
From Cats.Set Require Import Morphism.

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

(** ** Finite Covers

    A finite list of representatives covers the specified equality. Repeated
    representatives are allowed; neither decidable equality nor a choice
    principle is required. *)

(** ** 有限覆盖

    有限代表族按指定相等覆盖广集。允许重复代表，不要求可判定相等或选择公理。 *)

(** A chosen respectful enumeration and a representative for every element. *)

(** 选定的保相等枚举，以及每个元素的代表及相等见证。 *)

Class HasFiniteCover (X : SetC)
  :=
  { finite_count : nat
  ; finite_enum : FinS finite_count →r X
  ; finite_cover (x : X) : ∃ i, finite_enum i ≈S x
  }.

Arguments finite_count {_} {_}.
Arguments finite_enum {_} {_}.
Arguments finite_cover {_} {_} _.

(** Finite positions are covered by their identity enumeration. Enable this
    chosen structure explicitly. *)

(** 有限位置由恒等枚举覆盖；此选定结构须显式启用。 *)

Program Definition FinitePositionsCover (n : nat)
  : HasFiniteCover (FinS n)
  :=
  {|finite_count := n
  ; finite_enum := id_resp
  |}.
Next Obligation. exists x. reflexivity. Defined.
