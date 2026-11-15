From Cats Require Export Cat.Functor.ProductPreservation.
From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Exponential.Core.

(** * Exponential Comparisons without Terminal Preservation

    Binary-product preservation alone transports evaluation and currying.
    The comparison need not be invertible: no exponential preservation is
    assumed, and no terminal choices enter its construction. *)

(** * 不依赖终对象保持性的指数比较

    仅二元积保持性即可运输求值与柯里化。比较不一定可逆：构造不假设指数
    保持性，也不引入终对象选择。 *)

(** ** Comparing Evaluation and Transposition

    Fix products and exponentials on each side and a functor preserving
    the chosen source product cones. Transpose the transported evaluation;
    its naturality in the context is exactly the currying comparison law. *)

(** ** 比较求值与转置

    固定两侧的积和指数，以及保持来源选定积锥的函子。将运输后的求值转置；
    它在上下文上的自然性恰好给出柯里化比较律。 *)

Section ExponentialComparison.
Context {C D : Cat} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preserves : ∀ X Y : @Ob C,
    is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2)).

(** Curry the image evaluation after the inverse product comparison. *)

(** 将像求值与逆积比较的复合柯里化。 *)

Definition preserved_exponential_comparison (X Y : @Ob C)
  : Hom (F ((Y ^ X)%ob)) (F Y ^ F X)
  := ƛ (fmap F eval ∘ preserved_product_inv F preserves ((Y ^ X)%ob) X).

(** Evaluation recovers the transported evaluation map. *)

(** 求值恢复运输后的求值映射。 *)

Lemma preserved_eval (X Y : @Ob C)
  : eval ∘ (preserved_exponential_comparison X Y × id) ≈
      fmap F eval ∘ preserved_product_inv F preserves ((Y ^ X)%ob) X.
Proof. apply exponential_β. Qed.

(** Context substitution commutes with transposition through the comparison. *)

(** 经过比较时，上下文替换与转置交换。 *)

Lemma preserved_curry {X Y Z : @Ob C} (f : Hom (Z × X) Y)
  : preserved_exponential_comparison X Y ∘ fmap F (ƛ f) ≈
      ƛ (fmap F f ∘ preserved_product_inv F preserves Z X).
Proof.
  unfold preserved_exponential_comparison.
  rewrite <- exponential_curry_comp_r. apply exponential_curry_proper.
  rewrite <- (@functor_id C D F X).
  rewrite comp_assoc, <- preserved_product_inv_natural,
    <- comp_assoc, <- functor_comp.
  pose proof (@exponential_β C PC EC X Y Z f) as Hβ.
  unfold uncurry in Hβ. rewrite Hβ. reflexivity.
Qed.

End ExponentialComparison.
