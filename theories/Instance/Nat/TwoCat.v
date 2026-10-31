From Stdlib Require Import Arith.PeanoNat Lia.
From Cats Require Import Cat.Core Cat.Functor Cat.TwoCategory.

Local Open Scope nat_scope.

(** * A Bicategory from Addition

    There is one 0-cell and one 1-cell. The 2-cells are natural numbers;
    both compositions add them. Commutativity supplies interchange. Positive
    2-cells are not invertible, so this example is not locally a groupoid.
    The singleton 1-cell setoid gives a strict presentation. *)

Program Definition NatHomCat : Cat :=
  {| Ob := unit
   ; Hom _ _ := nat
   ; HomEq _ _ := eq
   ; id _ := 0
   ; comp _ _ _ m n := m + n
   |}.
Next Obligation. lia. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. lia. Defined.

Program Definition nat_horizontalF : Functor (NatHomCat ×C NatHomCat) NatHomCat :=
  {| F0 _ := tt
   ; F1 _ _ p := fst p + snd p
   |}.
Next Obligation. intros [a b] [a' b'] [Ha Hb]. cbn in *. now subst. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. destruct f, g. cbn. lia. Defined.

Program Definition NatBicat : Bicat :=
  {| ObB := unit
   ; HomCat _ _ := NatHomCat
   ; id1 _ := tt
   ; comp1F _ _ _ := nat_horizontalF
   ; associator _ _ _ _ _ _ _ := 0
   ; left_unitor _ _ _ := 0
   ; right_unitor _ _ _ := 0
   |}.
Next Obligation. exists 0. split; reflexivity. Defined.
Next Obligation. exists 0. split; reflexivity. Defined.
Next Obligation. exists 0. split; reflexivity. Defined.
Next Obligation. cbn. lia. Defined.
Next Obligation. cbn. lia. Defined.
Next Obligation. cbn. lia. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

Definition NatCell1Eq (X Y : ObB NatBicat)
    (f g : @Cell1 NatBicat X Y) := unit.

Definition nat_cell1_eq_to_cell2 X Y (f g : @Cell1 NatBicat X Y)
    (_ : NatCell1Eq X Y f g) : @Cell2 NatBicat X Y f g := 0.

Program Definition NatBicat_IsStrictTwoCat
  : IsStrictTwoCat NatBicat NatCell1Eq nat_cell1_eq_to_cell2 :=
  {| comp1_id_l _ _ _ := tt
   ; comp1_id_r _ _ _ := tt
   ; comp1_assoc _ _ _ _ _ _ _ := tt
   |}.
Next Obligation. split; red; intros; exact tt. Defined.
Next Obligation. intros g g' p f f' q. exact tt. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

Theorem nat_2cell_not_iso (n : nat) : 0 < n → ¬ @is_iso NatHomCat tt tt n.
Proof.
  intros H [m [Hm _]]. cbn in Hm. lia.
Qed.
