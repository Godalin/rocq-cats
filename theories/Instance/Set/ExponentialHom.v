From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Product.Core
  Cat.Exponential.Core.
From Cats Require Import
  Cat.Exponential.Currying.
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
  := adjunction_hom_nat_iso (ProdExpAdj X).

End ExponentialHom.

(** Flattening as a respectful map of native hom-setoids. *)

(** 展平作为原生 Hom 广集的保相等映射。 *)

Program Definition exponential_flatten_resp {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP}
    {A B Y Z : @Ob C}
  : HomSet Z ((Y ^ A) ^ B) →r HomSet Z (Y ^ (A × B))
  :=
  {|func := exponential_flatten
  |}.

(** Expanding as a respectful map of native hom-setoids. *)

(** 展开作为原生 Hom 广集的保相等映射。 *)

Program Definition exponential_expand_resp {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP}
    {A B Y Z : @Ob C}
  : HomSet Z (Y ^ (A × B)) →r HomSet Z ((Y ^ A) ^ B)
  :=
  {|func := exponential_expand
  |}.

(** The iterated exponential identity acts as an isomorphism on each
    native hom-setoid. Its context naturality is [exponential_flatten_comp]. *)

(** 迭代指数恒等在每个原生 Hom 广集上作为同构作用，其上下文自然性为
    [exponential_flatten_comp]。 *)

Definition exponential_iterated_hom_iso {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP}
    (A B Y Z : @Ob C)
  : HomSet Z ((Y ^ A) ^ B) ≅[SetCat] HomSet Z (Y ^ (A × B)).
Proof.
  exists exponential_flatten_resp, exponential_expand_resp. split;
    intros f; [apply exponential_flatten_β | apply exponential_flatten_η].
Defined.
