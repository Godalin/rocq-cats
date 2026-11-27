From Cats Require Import Cat.CCC.Core.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Cartesian
  Instance.Set.Exponential.

(** * The Cartesian Closed Category of Setoids *)

(** * 广集的笛卡尔闭范畴 *)

(** Extend the chosen cartesian setoid model by its exponentials. Enable
    this structure explicitly, retaining the same terminal and products. *)

(** 为选定笛卡尔广集模型增加指数；显式启用此结构，沿用相同终对象与积。 *)

Program Definition SetCat_CCC
  : CCC
  := CCCOfCartCat SetCat_Cart
      SetCat_HasExponential.

(** The fixed-category interface selects the same terminal object, products
    and exponentials as the bundled setoid model. *)

(** 固定范畴接口沿用广集模型选定的终对象、积和指数。 *)

Definition SetCat_HasCC : HasCC SetCat := CCCToHasCC SetCat_CCC.
