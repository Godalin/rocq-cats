From Cats Require Export Cat.Preorder.
From Cats Require Import Instance.Nat.Order.

(** * Finite Ordinals

    [n] has n+1 objects, numbered 0 through n, and one arrow i → j for i ≤ j. *)
Fixpoint OrdinalOb (n : nat) : Type :=
  match n with O => Empty_set | S n => unit + OrdinalOb n end.

Definition ordinal_first {n : nat} : OrdinalOb (S n) := inl tt.
Definition ordinal_next {n : nat} (i : OrdinalOb n) : OrdinalOb (S n) := inr i.

Fixpoint ordinal_rank {n : nat} : OrdinalOb n → nat :=
  match n as m return OrdinalOb m → nat with
  | O => λ i, match i with end
  | S m => λ i, match i with inl _ => O | inr j => S (@ordinal_rank m j) end
  end.

Definition OrdinalShape (n : nat) : Cat :=
  @PreorderCat (OrdinalOb (S n)) (λ i j, NatLe (ordinal_rank i) (ordinal_rank j))
    (pullback_preorder NatLe ordinal_rank).

Notation "'[Ord' n ']'" := (OrdinalShape n) : cat_scope.

Definition ordinal_from_first {n : nat} (i : OrdinalOb (S n))
  : (@Hom (OrdinalShape n)) ordinal_first i := tt.
