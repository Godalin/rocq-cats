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
    own products. The parent remains an inherited instance and the only
    underlying view; no terminal object or product is chosen twice. *)

(** 为一个选定笛卡尔结构增加相对于其自身积的指数。父结构同时作为继承实例
    和唯一底层视图，不重复选取终对象或积。 *)

Class CCC (C : Cat)
  :=
  (** Share the selected finite products with every weaker client. *)

  (** 与所有较弱的客户端共享选定有限积。 *)

  { hasCartesian :: CartesianCat C
  (** Exponentials use exactly the inherited choice of binary products. *)

  (** 指数恰好使用继承的二元积选择。 *)

  ; hasExponential :: HasExponential hasProduct
  }.

(** Register the parent projection as a coercion while retaining its
    instance role. The unique chain is [CCC] to [CartesianCat] to
    [Cat]; it computes to the named category [C]. *)

(** 将父结构投影同时注册为强制转换，并保留其实例职责。唯一转换链为 [CCC]
    经 [CartesianCat] 到 [Cat]，直接计算为具名范畴 [C]。 *)

Coercion hasCartesian : CCC >-> CartesianCat.
