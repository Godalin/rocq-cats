From Cats Require Import
  Cat.Core
  Cat.Preorder
  Cat.Terminal
  Cat.Product.Core
  Cat.Product.Componentwise
  Cat.Cartesian.Core.

(** * Basic Cartesian Category Constructions

    A pointed codiscrete category has chosen finite products, and products
    of cartesian categories inherit the componentwise choices. These are
    explicit bundles; importing them selects no model. *)

(** * 基本笛卡尔范畴构造

    带点余离散范畴具有选定有限积，笛卡尔范畴的乘积继承逐分量选择。
    这些都是显式结构包，导入不选择模型。 *)

(** Select the supplied point for the terminal object and every product. *)

(** 选择给定点作为终对象及每个积对象。 *)

Program Definition CodiscreteCart@{o h p l} (X : Type@{o}) (x : X)
  : CartCat@{l o h p l}
  := MakeCartCat (CodiscreteCat@{o h p l} X) {|Term := x|}
      {|Prod _ _ := x
      ; π1 _ _ := tt
      ; π2 _ _ := tt
      |}.
Next Obligation.
  intro Y. exists tt. split; [exact I |]. intros f _. exact tt.
Defined.
Next Obligation.
  intros Z f g. exists tt. split.
  - split; exact tt.
  - intros h _. exact tt.
Defined.

(** Pair the stored categories and reuse their selected universal witnesses. *)

(** 对保存的范畴配对，复用其选定泛性质见证。 *)

Program Definition ProdCart (C D : CartCat)
  : CartCat
  := MakeCartCat (C ×C D)
      (ProdCat_HasTerminal (hasTerminal C) (hasTerminal D))
      (ProdCat_HasProduct (hasProduct C) (hasProduct D)).
