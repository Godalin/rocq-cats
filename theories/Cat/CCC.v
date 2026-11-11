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
  (** The unique underlying view shares the selected finite products
      with every weaker client. *)

  (** 唯一底层视图与所有较弱的客户端共享选定有限积。 *)

  { CCCC :> CartesianCat C

  (** Exponentials use exactly the inherited choice of binary products. *)

  (** 指数恰好使用继承的二元积选择。 *)

  ; hasExponential :: HasExponential (@hasProduct C CCCC)
  }.

Arguments CCCC {_} _.

(** Also expose the same parent to instance search. The [:>] field
    already supplies the unique coercion chain through [CartesianCat]
    to [Cat]; instance registration selects no additional structure. *)

(** 同时将同一父结构提供给实例搜索。[:>] 字段已给出经 [CartesianCat]
    到 [Cat] 的唯一强制转换链；实例注册不再选择任何额外结构。 *)

#[export] Existing Instance CCCC.
