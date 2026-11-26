From Cats Require Export
  Cat.Cartesian.Core.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product.

(** * The Cartesian Category of Setoids *)

(** * 广集的笛卡尔范畴 *)

(** Bundle the existing terminal and product setoids. Pass this bundle to clients that take a cartesian category. *)

(** 打包已有终广集与积广集。此结构包可直接传给接收笛卡尔范畴的客户端。 *)

Program Definition SetCat_Cart
  : CartCat
  := MakeCartCat SetCat SetCat_HasTerminal SetCat_HasProduct.
