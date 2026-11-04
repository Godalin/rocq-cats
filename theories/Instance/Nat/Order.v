From Cats Require Import Cat.Preorder.
From Stdlib Require Import
  Arith.PeanoNat
  Lia.

(** * A Computational Order on Natural Numbers

    The comparison witness is in Type and computes to unit or Empty_set. *)

(** * 自然数上的可计算顺序

    比较见证位于 Type，计算为 [unit] 或 [Empty_set]。 *)

Fixpoint NatLe (n m : nat)
  : Type
  := match n, m with
  | O, _ => unit
  | S _, O => Empty_set
  | S n, S m => NatLe n m
  end.

(** Each natural number is below itself in the computational order. *)

(** 每个自然数在可计算顺序下小于等于自身。 *)

Definition nat_le_refl (n : nat)
  : NatLe n n.
Proof. induction n; cbn; [exact tt | exact IHn]. Defined.

(** Compose witnesses of the computational natural-number order. *)

(** 复合可计算自然数顺序的见证。 *)

Definition nat_le_trans {n m k : nat} (H : NatLe n m) (K : NatLe m k)
  : NatLe n k.
Proof.
  revert m k H K. induction n; intros m k H K; cbn in *; [exact tt |].
  destruct m; [destruct H |]. destruct k; [destruct K |].
  exact (IHn m k H K).
Defined.

(** [NatLe] is a preorder. *)

(** [NatLe] 是预序。 *)

Program Instance NatLe_PreOrder
  : PreOrder NatLe
  :=
  {|PreOrder_Reflexive := nat_le_refl
  ; PreOrder_Transitive n m k := @nat_le_trans n m k
  |}.

(** The thin category of natural numbers and computational order witnesses. *)

(** 以自然数及可计算顺序见证构成的薄范畴。 *)

Definition NatOrderCat
  := PreorderCat NatLe.

(** Computational order implies the usual arithmetic inequality. *)

(** 可计算顺序推出通常的算术不等式。 *)

Lemma nat_le_to_le {n m : nat} (H : NatLe n m)
  : n ≤ m.
Proof.
  revert m H. induction n; intros [|m] H; cbn in H; try lia.
  - destruct H.
  - specialize (IHn m H). lia.
Qed.

(** Recover a Type-valued order witness by recursion on the numbers.
    The arithmetic proof is used only to eliminate an impossible case. *)

(** 在自然数上递归恢复 Type 值顺序见证，算术证明只用于消去不可能的情形。 *)

Definition nat_le_of_le {n m : nat} (H : n ≤ m)
  : NatLe n m.
Proof.
  revert m H. induction n; intros [|m] H; cbn; try exact tt.
  - exfalso. lia.
  - apply IHn. lia.
Defined.
