From Cats.Set Require Export Core.

(** * Finite Positions

    The empty type and repeated finite sums give n positions without
    arithmetic bounds or proof fields. This concrete set uses native equality. *)
Fixpoint Fin (n : nat) : Type :=
  match n with O => Empty_set | S n => unit + Fin n end.

Definition fin_first {n : nat} : Fin (S n) := inl tt.
Definition fin_next {n : nat} (i : Fin n) : Fin (S n) := inr i.

Fixpoint fin_rank {n : nat} : Fin n → nat :=
  match n as m return Fin m → nat with
  | O => λ i, match i with end
  | S m => λ i, match i with inl _ => O | inr j => S (@fin_rank m j) end
  end.

Program Definition FinS@{u p +} (n : nat) : SetC@{u p} :=
  {| carrier := Fin n
   ; carrier_equiv x y := (x = y : Type@{p}) |}.
Next Obligation.
  split.
  - intros x. reflexivity.
  - intros x y H. symmetry. exact H.
  - intros x y z H K. transitivity y; assumption.
Defined.
