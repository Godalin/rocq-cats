From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Product.Sigma.
From Cats Require Export
  Cat.Coproduct.Indexed.

(** * Coproducts over Dependent Sums of Indices *)

(** * 依赖和索引上的余积 *)

(** Nested outer and fiberwise coproducts supply the dependent-sum coproduct.
    The stored data are the original opposite sigma-product construction. *)

(** 嵌套的外层与纤维余积给出依赖和余积，存储数据为原反依赖和积构造。 *)

Definition SigmaCoproductColimit {C : Cat} {I : Type} (J : I → Type)
    `{HO : !HasColimitsOfShape C (DiscreteCat I)}
    (HI : ∀ i, HasColimitsOfShape C (DiscreteCat (J i)))
    (D : Fct (DiscreteCat (∃ i, J i)) C)
  : HasColimit C D
  := @DiscreteDiagramColimit C (∃ i, J i) D
      (@SigmaProductLimit (C^op) I J (@DiscreteColimitsOpLimits C I HO)
        (λ i, @DiscreteColimitsOpLimits C (J i) (HI i))
        (D^opF ∘F OpDiscreteF (∃ i, J i))).

(** Choose all dependent-sum coproducts from the given outer and fiber choices. *)

(** 从给定外层与纤维选择，选择全部依赖和余积。 *)

Definition SigmaCoproductColimits {C : Cat} {I : Type}
    (J : I → Type) `{HO : !HasColimitsOfShape C (DiscreteCat I)}
    (HI : ∀ i, HasColimitsOfShape C (DiscreteCat (J i)))
  : HasColimitsOfShape C (DiscreteCat (∃ i, J i))
  := @OpDiscreteColimits C (∃ i, J i)
      (@SigmaProductLimits (C^op) I J (@DiscreteColimitsOpLimits C I HO)
        (λ i, @DiscreteColimitsOpLimits C (J i) (HI i))).
