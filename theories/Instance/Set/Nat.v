From Cats Require Import Cat.Core ETCS.Nat.
From Cats Require Import Instance.Set.Core Instance.Set.Terminal.

(** * A Natural-Numbers Object in Setoids *)

Program Definition NatS@{u r} : SetC@{u r} :=
  {| carrier := nat; carrier_equiv := @eq nat |}.
Next Obligation.
  split; red; intros; congruence.
Defined.

Program Definition zero_resp@{u r +} : UnitS@{u r} →r NatS@{u r} :=
  {| func _ := O |}.
Next Obligation. intros x y p. reflexivity. Defined.

Program Definition succ_resp@{u r +} : NatS@{u r} →r NatS@{u r} :=
  {| func := S |}.
Next Obligation. intros n m p. destruct p. reflexivity. Defined.

Program Definition nat_rec_resp@{u r +} {X : SetC@{u r}}
    (z : UnitS@{u r} →r X) (s : X →r X) : NatS@{u r} →r X :=
  {| func := fix iter (n : nat) : X :=
      match n with O => z tt | S m => s (iter m) end |}.
Next Obligation.
  intros n m p. destruct p. reflexivity.
Defined.

Program Definition SetCat_HasNaturalNumbersObject@{u r +}
  : HasNaturalNumbersObject SetCat@{u r _ _ _ _ _} SetCat_HasTerminal :=
  {| NNO := NatS; zero := zero_resp; succ := succ_resp |}.
Next Obligation.
  intros X z s. exists (nat_rec_resp z s). split.
  - split.
    + intros []. reflexivity.
    + intros n. reflexivity.
  - intros f [H0 Hsucc]. change (∀ n, f n ≈S nat_rec_resp z s n).
    fix IH 1. intros [|n].
    + exact (H0 tt).
    + change (f (S n) ≈S s (nat_rec_resp z s n)).
      transitivity (s (f n)). exact (Hsucc n). apply func_proper. exact (IH n).
Defined.
