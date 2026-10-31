From Stdlib Require Import Arith.PeanoNat Lia.
From Cats Require Import Cat.Core Cat.Functor Cat.Bicategory.

Local Open Scope nat_scope.

(** * A Bicategory from Addition

    There is one 0-cell and one 1-cell. The 2-cells are natural numbers;
    both compositions add them. Commutativity supplies interchange. Positive
    2-cells are not invertible, so this example is not locally a groupoid. *)

Definition NatHomCat : Cat.
Proof.
  refine (@Build_Cat unit (λ _ _, nat) (λ _ _, eq) (λ _ _, eq_equivalence)
    (λ _, 0) (λ _ _ _ m n, m + n)
    (λ _ _ _ a a' Ha b b' Hb, f_equal2 Nat.add Ha Hb) _ _ _).
  - intros X Y n. apply Nat.add_0_r.
  - intros X Y n. reflexivity.
  - intros W X Y Z a b c. lia.
Defined.

Definition nat_horizontalF : Functor (NatHomCat ×C NatHomCat) NatHomCat.
Proof.
  unshelve refine (@Build_Functor (NatHomCat ×C NatHomCat) NatHomCat
    (λ _, tt) (λ _ _ p, fst p + snd p) _ _ _).
  - intros X Y [a b] [a' b'] [Ha Hb]. cbn in *. now subst.
  - intros X. reflexivity.
  - intros X Y Z [a b] [c d]. cbn. lia.
Defined.

Definition NatBicat : Bicat.
Proof.
  refine (@Build_Bicat unit (λ _ _, NatHomCat) (λ _, tt) (λ _ _ _, nat_horizontalF)
    (λ _ _ _ _ _ _ _, 0) _ (λ _ _ _, 0) _ (λ _ _ _, 0) _ _ _ _ _ _).
  - intros W X Y Z h g f. exists 0. split; reflexivity.
  - intros X Y f. exists 0. split; reflexivity.
  - intros X Y f. exists 0. split; reflexivity.
  - intros W X Y Z h h' g g' f f' γ β α. cbn. lia.
  - intros X Y f g α. cbn. lia.
  - intros X Y f g α. cbn. lia.
  - intros V W X Y Z k h g f. reflexivity.
  - intros X Y Z g f. reflexivity.
Defined.

Theorem nat_2cell_not_iso (n : nat) : 0 < n → ¬ @is_iso NatHomCat tt tt n.
Proof.
  intros H [m [Hm _]]. cbn in Hm. lia.
Qed.
