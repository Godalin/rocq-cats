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

Record Topos
  := ToposOfCCC

  (** Share the selected finite products and exponentials through one
      immediate parent, without choosing any of them again. *)

  (** 通过唯一直接父结构共享选定的有限积和指数，不重复作出选择。 *)

  { ToposToCCC :> CCC

  (** Together with the inherited finite products, pullbacks provide
      finite limits. *)

  (** 拉回与继承的有限积共同给出有限极限。 *)

  ; hasPullback :: HasPullback ToposToCCC

  (** Classify subobjects relative to that same terminal choice. *)

  (** 相对于同一终对象选择分类子对象。 *)

  ; hasSubObjClassifier
    :: HasSubObjClassifier ToposToCCC
        (hasTerminal ToposToCCC)
  }.
