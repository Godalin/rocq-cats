From Cats Require Export
  Cat.CCC.Core
  Topos.Sub.
From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Pullback.

(** * Elementary Toposes *)

(** * 初等拓扑斯 *)

(** Extend a chosen cartesian closed category by pullbacks and a subobject
    classifier. The classifier uses the parent's selected terminal object.
    Well-pointedness, choice and natural numbers are additional structures,
    not requirements of an elementary topos. *)

(** 为一个选定笛卡尔闭范畴增加拉回和子对象分类子。
    分类子使用父结构选定的终对象；良点性、选择和自然数是额外结构，
    并非初等拓扑斯的要求。 *)

(** Store each chosen component once. Pullbacks together with the inherited
    products give finite limits; classification uses the inherited terminal. *)

(** 每项选定成分只保存一次。拉回与继承的积给出有限极限；分类使用继承的终对象。 *)

Minks.Struct Topos
  extends CCC
  with  hasPullback as hasPullback : HasPullback,
        hasSubObjClassifier as hasSubObjClassifier : HasSubObjClassifier.
