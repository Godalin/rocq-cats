From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Exponential.Core.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Product.

(** * Exponentials of Setoids

    The exponential consists of respectful maps with pointwise equivalence. *)

(** * 广集的指数对象

    指数由保相等映射组成，相等按逐点指定相等比较。 *)

Program Definition eval_resp {X Y : SetC}
  : (X →S Y) ×S X →r Y
  :=
  {|func p := (fst p) (snd p)
  |}.
Next Obligation.
  intros [f x] [g y] [Hfg Hxy].
  transitivity (g x). exact (Hfg x). apply func_proper. exact Hxy.
Defined.

(** Curry a respectful map of setoid products. *)

(** 对广集乘积上的保相等映射柯里化。 *)

Program Definition curry_resp {X Y Z : SetC} (f : Z ×S X →r Y)
  : Z →r (X →S Y)
  :=
  {|func z :=
     {|func x := f (z, x)
     |}
  |}.
Next Obligation.
  intros x x' Hx. apply func_proper. split; [reflexivity | exact Hx].
Defined.
Next Obligation.
  intros z z' Hz x. change (f (z, x) ≈S f (z', x)).
  apply func_proper. split; [exact Hz | reflexivity].
Defined.

Local Existing Instance SetCat_HasProduct.

(** Choose respectful-function setoids as exponential objects. *)

(** 选择保相等函数广集作为指数对象。 *)

Program Definition SetCat_HasExponential
  : @HasExponential SetCat SetCat_HasProduct
  :=
  {|exp Y X := X →S Y
  ; eval X Y := eval_resp (X := X) (Y := Y)
  |}.
Next Obligation.
  intros Z f. exists (curry_resp f). split.
  - rewrite cross_η. intros [z x]. reflexivity.
  - intros h Hh z x. rewrite cross_η in Hh. exact (Hh (z, x)).
Defined.
