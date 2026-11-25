From Cats Require Export
  Cat.Cartesian.Core.
From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core.

(** * Cartesian Closed Category *)

(** * 笛卡尔闭范畴 *)

(** Extend one chosen cartesian structure by exponentials relative to its
    own products. The parent is the only
    underlying view; no terminal object or product is chosen twice. *)

(** 为一个选定笛卡尔结构增加相对于其自身积的指数。父结构作为唯一底层视图，不重复选取终对象或积。 *)

Minks.Struct CCC@{o h p l t}
  extends CartCat@{t o h p l}
  with  hasExponential as hasExponential : HasExponential.
