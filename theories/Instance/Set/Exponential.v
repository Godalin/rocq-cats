From Cats Require Import Cat.Core Cat.Product Cat.Exponential.
From Cats Require Import Instance.Set.Core Instance.Set.Product.

(** * Exponentials of Setoids

    The exponential consists of respectful maps with pointwise equivalence. *)

Program Definition eval_resp {X Y : SetC} : ProdS (FunS X Y) X →r Y :=
  {| func p := (fst p) (snd p) |}.
Next Obligation.
  intros [f x] [g y] [Hfg Hxy].
  transitivity (g x). exact (Hfg x). apply func_proper. exact Hxy.
Defined.

Program Definition curry_resp {X Y Z : SetC} (f : ProdS Z X →r Y)
  : Z →r FunS X Y := {| func z := {| func x := f (z, x) |} |}.
Next Obligation.
  intros x x' Hx. apply func_proper. split; [reflexivity | exact Hx].
Defined.
Next Obligation.
  intros z z' Hz x. change (f (z, x) ≈S f (z', x)).
  apply func_proper. split; [exact Hz | reflexivity].
Defined.

Local Existing Instance SetCat_HasProduct.

Program Definition SetCat_HasExponential : @HasExponential SetCat SetCat_HasProduct :=
  {| exp Y X := FunS X Y
   ; eval X Y := eval_resp (X := X) (Y := Y) |}.
Next Obligation.
  intros Z f. exists (curry_resp f). split.
  - rewrite cross_η. intros [z x]. reflexivity.
  - intros h Hh z x. rewrite cross_η in Hh. exact (Hh (z, x)).
Defined.
