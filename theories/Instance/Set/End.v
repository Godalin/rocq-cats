From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Arrow.Core
  Cat.Diagram.Discrete
  Cat.End.Construction
  Instance.Set.Core
  Instance.Set.Limit
  Instance.Set.Equalizer.

(** * Ends in the Category of Setoids *)

(** * 广集范畴中的 end *)

(** Instantiate the abstract construction with the existing dependent-product
    and equalizer models. Sufficient bounds are [o,h ≤ p ≤ u]: both product
    index types fit the equality level, and equalizer evidence fits the carrier
    level. The index category's hom-equality level [e] stays independent.
    These are bounds for this construction, not necessary conditions for every
    possible end model. No structure is selected globally by importing this
    module, and no equality of witness fields is required. *)

(** 用已有依赖积和等化子模型实例化抽象构造。充分大小界为 [o,h ≤ p ≤ u]：两个
    积指标类型都容纳于相等层级，等化子证据容纳于载体层级。指标范畴的 Hom 相等
    层级 [e] 保持独立。这些是本构造的大小界，不是所有可能 end 模型的必要条件。
    导入本模块不全局选择结构，也不要求见证字段相等。 *)

Definition SetCat_End@{o h e u p +} (C : Cat@{o h e _ _})
    (F : Functor ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}))
  : HasEnd SetCat F
  := @ProductsEqualizerEnd C SetCat F
      (SetCat_IndexedProductLimit (DiscreteF (EndDiagonal F)))
      (SetCat_IndexedProductLimit (DiscreteF (EndTargets F)))
      SetCat_HasEqualizer.
