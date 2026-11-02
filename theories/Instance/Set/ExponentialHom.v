From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Product
  Cat.Exponential.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Adjunction.

(** * Exponential Hom-Setoid Correspondence

    The source category is arbitrary. [SetCat] is used only to express an
    isomorphism of its hom-setoids; no chosen setoid CCC model is enabled.
    Naturality in the context and result object is expressed by
    [exponential_curry_comp_r] and [exponential_curry_comp_l]. *)

(** * 指数的 Hom 广集对应

    源范畴任意，[SetCat] 只用于表示 Hom 广集同构，不启用具体广集的选定笛卡尔闭
    模型。上下文和结果对象上的自然性由 [exponential_curry_comp_r] 与
    [exponential_curry_comp_l] 表达。 *)

Section ExponentialHom.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Currying and uncurrying give an isomorphism of native hom-setoids. *)

(** 柯里化与反柯里化给出原生 Hom 广集同构。 *)

Definition exponential_hom_iso {X Y Z : @Ob C}
  : HomSet (Z × X) Y ≅[SetCat] HomSet Z (Y ^ X).
Proof.
  exists exponential_curry_resp, exponential_uncurry_resp. split.
  - intros f. apply exponential_β.
  - intros g. apply exponential_η.
Defined.

(** The exponential hom-setoid correspondence is natural in context and
    result. *)

(** 指数 Hom 广集对应在上下文和结果对象上自然。 *)

Definition exponential_hom_nat_iso@{u p +} (X : @Ob C)
  : @NatIso _ SetCat@{u p _ _ _ _ _}
      (LeftHomF (-× X)) (RightHomF (-^ X))
  := adjunction_hom_nat_iso (ProductExponentialAdjunction X).

End ExponentialHom.
