From Cats Require Export
  Cat.Gluing.Terminal
  Cat.Comma.Product
  Cat.Cartesian.Core.
From Cats Require Import Cat.Functor.Cartesian.

(** * Finite Products in Gluing

    A base terminal object and binary products on both sides suffice,
    provided [F] preserves the selected base product cones. Terminal
    preservation is not needed for the glued category or its right
    projection. Only terminal preservation by the left projection needs
    the additional terminality of [F 1]. No chosen structures are enabled
    globally by importing this module. *)

(** * 粘合中的有限积

    基范畴的终对象与两侧的二元积已经足够，条件是 [F] 保持选定的基积锥。
    粘合范畴及其右投影不要求终对象保持性。只有左投影的终对象保持性才需要
    额外要求 [F 1] 为终。导入本模块不会全局启用任何选定结构。 *)

(** ** Binary Products without Terminal Assumptions

    Fix a functor, two binary-product choices and preservation of the
    source cones. Instantiate the general comma theorem with the identity
    on the left; no new universal-property proof is necessary. *)

(** ** 不带终对象假设的二元积

    固定函子、两个二元积选择及来源锥的保持性。将通用逗号定理的左函子取为
    恒等，无须再证明泛性质。 *)

Section GluingProducts.
Context {C D : Cat} (F : Fct C D).
Context `{PC : !HasProduct C} `{PD : !HasProduct D}.
Context (preserves : ∀ A B : @Ob C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).

(** Explicitly select the products already constructed in the comma theory. *)

(** 显式选择逗号理论中已经构造的积。 *)

Definition Gluing_HasProduct
  : HasProduct (Gluing F)
  := Comma_HasProduct IdF F preserves.

(** Both left projection legs are exactly the selected target legs. *)

(** 左投影的两条锥腿恰为选定目标锥腿。 *)

Definition gluing_left_product (X Y : @Ob (Gluing F))
  : is_product (GluingLeftF F X) (GluingLeftF F Y)
      (GluingLeftF F (@Prod _ Gluing_HasProduct X Y))
      (fmap (GluingLeftF F)
        (@Cats.Cat.Product.Core.π1 _ Gluing_HasProduct X Y))
      (fmap (GluingLeftF F)
        (@Cats.Cat.Product.Core.π2 _ Gluing_HasProduct X Y))
  := product_universal.

(** The right projection preserves the supplied base product cone. *)

(** 右投影保持给定的基积锥。 *)

Definition gluing_right_product (X Y : @Ob (Gluing F))
  : is_product (GluingRightF F X) (GluingRightF F Y)
      (GluingRightF F (@Prod _ Gluing_HasProduct X Y))
      (fmap (GluingRightF F)
        (@Cats.Cat.Product.Core.π1 _ Gluing_HasProduct X Y))
      (fmap (GluingRightF F)
        (@Cats.Cat.Product.Core.π2 _ Gluing_HasProduct X Y))
  := product_universal.

End GluingProducts.

(** ** Cartesian Structure and Projections

    Add a chosen base terminal object to the preceding binary-product
    assumptions. The right projection preserves finite products outright;
    the left projection separately records its exact extra hypothesis. *)

(** ** 笛卡尔结构与投影

    在上述二元积假设之外加入选定的基终对象。右投影直接保持有限积；左投影
    则单独记录其精确的额外假设。 *)

Section GluingCartesian.
Context {C D : Cat} (F : Fct C D).
Context `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{PD : !HasProduct D}.
Context (preserves : ∀ A B : @Ob C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).

(** The bundle reuses the independently constructed choices. *)

(** 此打包复用独立构造的选择。 *)

Program Definition Gluing_CartCat
  : CartCat
  := MakeCartCat (Gluing F)
      (Gluing_HasTerminal F)
      (Gluing_HasProduct F preserves).

(** The base projection preserves both selected structures. *)

(** 基投影保持两个选定结构。 *)

Program Definition GluingRight_IsCartF
  : IsCartF (GluingRightF F) (Gluing_HasTerminal F)
      (Gluing_HasProduct F preserves)
  :=
  {|fct_terminal := terminal_universal
  ; fct_product := gluing_right_product F preserves
  |}.

(** Left preservation requires the image terminal to be terminal in [D].
    No particular chosen terminal in [D] is required. *)

(** 左侧保持性要求终对象的像在 [D] 中为终；不需要 [D] 中有特定选定终对象。 *)

Program Definition GluingLeft_IsCartF (image_terminal : is_terminal (F 1))
  : IsCartF (GluingLeftF F) (Gluing_HasTerminal F)
      (Gluing_HasProduct F preserves)
  :=
  {|fct_terminal := image_terminal
  ; fct_product := gluing_left_product F preserves
  |}.

End GluingCartesian.
