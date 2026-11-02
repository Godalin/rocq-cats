From Cats Require Import
  Cat.Core
  ETCS.Nat.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal.

(** * A Natural-Numbers Object in Setoids *)

(** * 广集中的自然数对象 *)

(** Natural numbers with native equality as the specified setoid equality. *)

(** 以原生相等作为指定相等的自然数广集。 *)

Program Definition NatS@{u r}
  : SetC@{u r}
  :=
  {|carrier := nat
  ; carrier_equiv := @eq nat
  |}.
Next Obligation.
  split; red; intros; congruence.
Defined.

(** Zero as a respectful map from the terminal setoid. *)

(** 从终广集出发、取值为零的保相等映射。 *)

Program Definition zero_resp@{u r +}
  : UnitS@{u r} →r NatS@{u r}
  :=
  {|func _ := O
  |}.
Next Obligation. intros x y p. reflexivity. Defined.

(** Successor as a respectful natural-number map. *)

(** 后继作为自然数广集的保相等映射。 *)

Program Definition succ_resp@{u r +}
  : NatS@{u r} →r NatS@{u r}
  :=
  {|func := S
  |}.
Next Obligation. intros n m p. destruct p. reflexivity. Defined.

(** The respectful map defined by natural-number recursion. *)

(** 自然数递归定义的保相等映射。 *)

Program Definition nat_rec_resp@{u r +} {X : SetC@{u r}}
    (z : UnitS@{u r} →r X) (s : X →r X)
  : NatS@{u r} →r X
  :=
  {|func := fix iter (n : nat) : X :=
     match n with O => z tt | S m => s (iter m) end
  |}.
Next Obligation.
  intros n m p. destruct p. reflexivity.
Defined.

(** Choose the ordinary natural-number setoid as a natural-numbers object. *)

(** 选择普通自然数广集作为自然数对象。 *)

Program Definition SetCat_HasNaturalNumbersObject@{u r +}
  : HasNaturalNumbersObject SetCat@{u r _ _ _ _ _} SetCat_HasTerminal
  :=
  {|NNO := NatS
  ; zero := zero_resp
  ; succ := succ_resp
  |}.
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
