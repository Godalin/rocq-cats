From Stdlib Require Import
  Arith.PeanoNat
  Lia.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Bicategory.Strict.

Local Open Scope nat_scope.

(** * A Bicategory from Addition

    There is one 0-cell and one 1-cell. The 2-cells are natural numbers; both
    compositions add them. Commutativity supplies interchange. Positive
    2-cells are not invertible, so this example is not locally a groupoid. The
    singleton 1-cell setoid gives a strict presentation. *)

(** * 由加法构造双范畴

    仅有一个零胞与一个一胞，二胞是自然数，水平与垂直复合都用加法，交换律保证交
    换律图成立。正二胞不可逆，故此例并非局部群胚；单元素一胞广集给出严格表示。 *)

Program Definition NatHomCat
  : Cat
  :=
  {|Ob := unit
  ; HomSet _ _ :=
      {|carrier := nat
      ; carrier_equiv := eq
      ; carrier_setoid := eq_equivalence
      |}
  ; id _ := 0
  ; comp _ _ _ m n := m + n
  |}.
Next Obligation. lia. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. lia. Defined.

(** Add the two natural-number two-cells to compose horizontally. *)

(** 将两个自然数二胞相加，给出水平复合。 *)

Program Definition nat_horizontalF
  : Functor (NatHomCat ×C NatHomCat) NatHomCat
  :=
  {|F0 _ := tt
  ; F1 _ _ p := fst p + snd p
  |}.
Next Obligation. intros [a b] [a' b'] [Ha Hb]. cbn in *. now subst. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. destruct f, g. cbn. lia. Defined.

(** One zero-cell and one one-cell, with natural numbers as additive
    two-cells. *)

(** 一个零胞和一个一胞，二胞为按加法复合的自然数。 *)

Program Definition NatBicat
  : Bicat
  :=
  {|ObB := unit
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

(** The specified equality of the singleton one-cell carrier. *)

(** 单元素一胞载体上的指定相等。 *)

Definition NatCell1Eq (X Y : ObB NatBicat)
    (f g : @Cell1 NatBicat X Y)
  := unit.

(** A one-cell equality is represented by the zero two-cell. *)

(** 用零二胞表示一胞相等。 *)

Definition nat_cell1_eq_to_cell2 X Y (f g : @Cell1 NatBicat X Y)
    (_ : NatCell1Eq X Y f g)
  : @Cell2 NatBicat X Y f g
  := 0.

(** The natural-number bicategory is strict relative to its singleton one-cell
    setoid. *)

(** 自然数双范畴相对于单元素一胞广集是严格的。 *)

Program Definition NatBicat_IsStrictTwoCat
  : IsStrictTwoCat NatBicat NatCell1Eq nat_cell1_eq_to_cell2
  :=
  {|comp1_id_l _ _ _ := tt
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

(** A positive natural-number two-cell has no additive inverse. *)

(** 正自然数二胞没有加法逆。 *)

Theorem nat_2cell_not_iso (n : nat)
  : 0 < n → ¬ @is_iso NatHomCat tt tt n.
Proof.
  intros H [m [Hm _]]. cbn in Hm. lia.
Qed.
