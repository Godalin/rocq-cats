From Cats.Set Require Export Finite.
From Cats Require Export Cat.Preorder.
From Cats Require Import Instance.Nat.Order.

(** * Finite Ordinals

    [n] has n+1 objects, numbered 0 through n, and one arrow i → j for i ≤
    j. *)

(** * 有限序数

    [n] 对应从零到 n 的 n+1 个对象；当 i ≤ j 时存在唯一箭头 i → j。 *)

Definition OrdinalShape (n : nat)
  : Cat
  := @PreorderCat (Fin (S n)) (λ i j, NatLe (fin_rank i) (fin_rank j))
    (pullback_preorder NatLe fin_rank).

Notation "'[Ord' n ']'" := (OrdinalShape n) : cat_scope.

(** The unique arrow from the least finite ordinal position. *)

(** 从有限序数最小位置出发的唯一箭头。 *)

Definition ordinal_from_first {n : nat} (i : Fin (S n))
  : (@Hom (OrdinalShape n)) fin_first i
  := tt.
