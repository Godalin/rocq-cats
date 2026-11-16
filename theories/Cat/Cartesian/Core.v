From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core.

(** * Cartesian Categories *)

(** * 笛卡尔范畴 *)

(** A category with chosen finite products. A terminal object
    supplies the empty product, and binary products supply the remaining
    finite products. The universal properties retain their Type-valued
    computational witnesses. *)

(** 带有选定有限积的范畴。终对象给出空积，二元积给出其余有限积；
    泛性质保留 Type 值的计算见证。 *)

Record CartCat
  := CartCatOfCat

  (** Store the unique underlying category once. *)

  (** 仅保存一份唯一底层范畴。 *)

  { CartCatToCat :> Cat

  (** Select the terminal object and its full universal property. *)

  (** 选定终对象及其完整泛性质。 *)

  ; hasTerminal :: HasTerminal CartCatToCat

  (** Select binary products, projections and universal mediators. *)

  (** 选定二元积、投影与泛中介。 *)

  ; hasProduct :: HasProduct CartCatToCat

  }.
