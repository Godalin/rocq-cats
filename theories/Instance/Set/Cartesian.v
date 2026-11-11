From Cats Require Export
  Cat.Cartesian.Core.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product.

(** * The Cartesian Category of Setoids *)

(** * 广集的笛卡尔范畴 *)

(** Bundle the existing terminal and product setoids. Enable this chosen
    structure explicitly; importing it does not select a model instance. *)

(** 打包已有终广集与积广集。这个选定结构须显式启用；导入时不自动选取
    模型实例。 *)

Program Definition SetCat_Cartesian
  : CartesianCat SetCat
  :=
  {|hasTerminal := SetCat_HasTerminal
  ; hasProduct := SetCat_HasProduct
  |}.
