From Cats Require Import Cat.CCC.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal.
From Cats Require Import
  Instance.Set.Product
  Instance.Set.Exponential.

(** * The Cartesian Closed Category of Setoids *)

(** * 广集的笛卡尔闭范畴 *)

(** Explicitly bundle the chosen terminal, product and exponential setoid
    models. *)

(** 显式组合广集的选定终对象、积与指数模型。 *)

Program Definition SetCat_CCC
  : CCC SetCat
  :=
  {|hasTerminal := SetCat_HasTerminal
  ; hasProduct := SetCat_HasProduct
  ; hasExponential := SetCat_HasExponential
  |}.
