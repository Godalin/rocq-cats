From Cats Require Import Cat.Core ETCS.Nat.
From Cats Require Import Instance.Set.Core Instance.Set.Terminal.

(** * A Natural-Numbers Object in Setoids *)

Definition NatS@{u r} : SetC@{u r}.
Proof.
  refine {| carrier := nat; carrier_equiv := @eq nat |}.
  split; red; intros; congruence.
Defined.

Definition zero_resp@{u r +} : UnitS@{u r} →r NatS@{u r} :=
  @Build_FunS_resp UnitS@{u r} NatS@{u r}
    (λ _, O) (λ _ _ _, eq_refl O).

Definition succ_resp@{u r +} : NatS@{u r} →r NatS@{u r} :=
  @Build_FunS_resp NatS@{u r} NatS@{u r} S (λ n m p, f_equal S p).

Definition nat_rec_resp@{u r +} {X : SetC@{u r}}
    (z : UnitS@{u r} →r X) (s : X →r X) : NatS@{u r} →r X.
Proof.
  unshelve refine (@Build_FunS_resp NatS@{u r} X
    (fix iter (n : nat) : X :=
      match n with O => z tt | S m => s (iter m) end) _).
  intros n m p. destruct p. reflexivity.
Defined.

Definition SetCat_HasNaturalNumbersObject@{u r +}
  : HasNaturalNumbersObject SetCat@{_ _ _ _ _ u r} SetCat_HasTerminal.
Proof.
  refine (@Build_HasNaturalNumbersObject SetCat SetCat_HasTerminal
    NatS zero_resp succ_resp _).
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
