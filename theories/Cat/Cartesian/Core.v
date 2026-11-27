From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core.

(** * Cartesian Categories *)

(** * 笛卡尔范畴 *)

(** A category with chosen finite products. A terminal object
    supplies the empty product, and binary products supply the remaining
    finite products. The universal properties retain their Type-valued
    computational witnesses. The terminal witness and the category laws may
    live at different universe levels. [HasCartesian C] groups these choices
    on a fixed category [C]. *)

(** 带有选定有限积的范畴。终对象给出空积，二元积给出其余有限积；
    泛性质保留 Type 值的计算见证。终对象见证与范畴定律可以位于不同的宇宙层级。
    [HasCartesian C] 将固定范畴 [C] 上的这些选择打包。 *)

Minks.Struct CartCat
  extends Cat
  with  hasTerminal as hasTerminal : HasTerminal,
        hasProduct as hasProduct : HasProduct
  exports HasCartesian [carrier].
