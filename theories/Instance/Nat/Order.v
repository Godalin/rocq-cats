From Cats Require Import Cat.Preorder.

(** * A Computational Order on Natural Numbers

    The comparison witness is in Type and computes to unit or Empty_set. *)
Fixpoint NatLe (n m : nat) : Type :=
  match n, m with
  | O, _ => unit
  | S _, O => Empty_set
  | S n, S m => NatLe n m
  end.

Definition nat_le_refl (n : nat) : NatLe n n.
Proof. induction n; cbn; [exact tt | exact IHn]. Defined.

Definition nat_le_trans {n m k : nat} (H : NatLe n m) (K : NatLe m k) : NatLe n k.
Proof.
  revert m k H K. induction n; intros m k H K; cbn in *; [exact tt |].
  destruct m; [destruct H |]. destruct k; [destruct K |].
  exact (IHn m k H K).
Defined.

Program Instance NatLe_PreOrder : PreOrder NatLe :=
  {| PreOrder_Reflexive := nat_le_refl
   ; PreOrder_Transitive n m k := @nat_le_trans n m k |}.

Definition NatOrderCat := PreorderCat NatLe.
