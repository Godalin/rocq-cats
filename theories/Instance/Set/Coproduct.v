From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Coproduct.Core
  Instance.Set.Core.
From Cats.Set Require Export
  Sum.

(** * Coproducts in the Category of Setoids *)

(** * 广集范畴中的余积 *)

(** Choose disjoint sums through the original opposite product structure.
    Importing this module does not enable the choice globally. *)

(** 通过原反积结构选择不交和；导入本模块不在全局启用该选择。 *)

Program Definition SetCat_HasCoproduct@{u p +}
  : HasCoproduct (SetCat@{u p _ _ _ _ _})
  :=
  {|hasOpProduct :=
      {|Prod := SumS
      ; π1 X Y := inl_resp
      ; π2 X Y := inr_resp
      |}
  |}.
Next Obligation.
  intros Z f g. exists (sum_case_resp f g).
  refine {|this := _
         ; that := _
         |}.
  - split; intros x; reflexivity.
  - intros h [H1 H2] [x | y]; [exact (H1 x) | exact (H2 y)].
Defined.
