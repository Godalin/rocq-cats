From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core.

(** * Finite-Product Cones in Product Categories

    Terminal objects and binary-product cones combine componentwise.
    Keep their candidate universal properties separate from the chosen
    structures, so preservation arguments reuse the same witnesses. *)

(** * 乘积范畴中的有限积锥

    终对象及二元积锥逐分量组合。将候选泛性质与选定结构分开，
    使保持性论证能复用同一组见证。 *)

(** Two terminal candidates form a terminal object in the product category. *)

(** 两个终候选组成乘积范畴中的终对象。 *)

Definition prod_is_terminal {C D : Cat} {T : C} {U : D}
    (HT : is_terminal T) (HU : is_terminal U)
  : @is_terminal (C ×C D) (T, U).
Proof.
  intros [X Y].
  destruct (HT X) as [f [_ Hf]], (HU Y) as [g [_ Hg]].
  exists (f, g). split; [exact I |]. intros [h k] _.
  split; [apply Hf | apply Hg]; exact I.
Defined.

(** Product cones combine without selecting any other products. *)

(** 积锥的组合不需要选取其他积。 *)

Definition prod_is_product {C D : Cat}
    {X Y P : C} {X' Y' P' : D}
    {p : Hom P X} {q : Hom P Y}
    {p' : Hom P' X'} {q' : Hom P' Y'}
    (HP : is_product X Y P p q) (HP' : is_product X' Y' P' p' q')
  : @is_product (C ×C D) (X, X') (Y, Y') (P, P') (p, p') (q, q').
Proof.
  intros [Z Z'] [f f'] [g g'].
  destruct (HP Z f g) as [h [[H1 H2] Hu]].
  destruct (HP' Z' f' g') as [h' [[H1' H2'] Hu']].
  exists (h, h'). split.
  - split; split; assumption.
  - intros [k k'] [[K1 K1'] [K2 K2']].
    split; [apply Hu | apply Hu']; split; assumption.
Defined.

(** Select the componentwise terminal object with the same mediators. *)

(** 逐分量选择终对象，保留原泛中介。 *)

Program Definition ProdCat_HasTerminal {C D : Cat}
    (TC : HasTerminal C) (TD : HasTerminal D)
  : HasTerminal (C ×C D)
  :=
  {|Term := (@Term C TC, @Term D TD)
  ; terminal_universal := prod_is_terminal
      (@terminal_universal C TC) (@terminal_universal D TD)
  |}.

(** Select componentwise binary products and their original projections. *)

(** 逐分量选择二元积及原投影。 *)

Program Definition ProdCat_HasProduct {C D : Cat}
    (PC : HasProduct C) (PD : HasProduct D)
  : HasProduct (C ×C D)
  :=
  {|Prod X Y := (@Prod C PC (fst X) (fst Y), @Prod D PD (snd X) (snd Y))
  ; π1 X Y := (@Cats.Cat.Product.Core.π1 C PC _ _,
      @Cats.Cat.Product.Core.π1 D PD _ _)
  ; π2 X Y := (@Cats.Cat.Product.Core.π2 C PC _ _,
      @Cats.Cat.Product.Core.π2 D PD _ _)
  ; product_universal X Y := prod_is_product
      (@product_universal C PC _ _) (@product_universal D PD _ _)
  |}.
