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
    own products. [HasCC C] exposes the terminal object, products and
    exponentials together on a fixed category [C]. *)

(** 为一个选定笛卡尔结构增加相对于其自身积的指数。[HasCC C] 将固定范畴 [C]
    上的终对象、积与指数一起导出。 *)

Minks.Struct CCC@{o h p l t}
  extends CartCat@{t o h p l}
  with  hasExponential as hasExponential : HasExponential
  exports HasCC [carrier].
