From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core.

(** * Cartesian Categories *)

(** * 笛卡尔范畴 *)

(** Chosen finite products on the named category [C]. A terminal object
    supplies the empty product, and binary products supply the remaining
    finite products. The universal properties retain their Type-valued
    computational witnesses. *)

(** 具名范畴 [C] 上选定的有限积。终对象给出空积，二元积给出其余有限积；
    泛性质保留 Type 值的计算见证。 *)

Class CartesianCat (C : Cat)
  :=
  (** The unique category view computes to the supplied parameter;
      no second category is stored. *)

  (** 唯一范畴视图直接计算为给定参数，不另存一个范畴。 *)

  { CartesianC :> Cat := C

  (** Select the terminal object and its full universal property. *)

  (** 选定终对象及其完整泛性质。 *)

  ; hasTerminal :: HasTerminal C

  (** Select binary products, projections and universal mediators. *)

  (** 选定二元积、投影与泛中介。 *)

  ; hasProduct :: HasProduct C
  }.

Arguments CartesianC {_} _.
