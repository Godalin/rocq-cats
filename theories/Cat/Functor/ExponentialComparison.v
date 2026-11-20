From Cats Require Export Cat.Functor.ProductPreservation.
From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Functor.Cartesian.

(** * Exponential Comparisons without Terminal Preservation

    Binary-product preservation alone transports evaluation and currying.
    The comparison need not be invertible: no exponential preservation is
    assumed, and no terminal choices enter its construction. *)

(** * 不依赖终对象保持性的指数比较

    仅二元积保持性即可运输求值与柯里化。比较不一定可逆：构造不假设指数
    保持性，也不引入终对象选择。 *)

Local Open Scope ob_scope.

(** ** Comparing Evaluation and Transposition

    Fix products and exponentials on each side and a functor preserving
    the chosen source product cones. Transpose the transported evaluation;
    its naturality in the context is exactly the currying comparison law. *)

(** ** 比较求值与转置

    固定两侧的积和指数，以及保持来源选定积锥的函子。将运输后的求值转置；
    它在上下文上的自然性恰好给出柯里化比较律。 *)

Section ExponentialComparison.
Context {C D : Cat} (F : Fct C D).
Context
  `{PC : !HasProduct C} `{EC : !HasExponential PC}
  `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context
  (preserves : ∀ X Y : C,
    is_product (F X) (F Y) (F (X × Y)) (fmap F π1) (fmap F π2)).

(** Curry the image evaluation after the inverse product comparison. *)

(** 将像求值与逆积比较的复合柯里化。 *)

Definition exp_cmp (X Y : C)
  : Hom (F (Y ^ X)) (F Y ^ F X)
  := ƛ (fmap F eval ∘ preserved_product_inv F preserves (Y ^ X) X).

(** Evaluation recovers the transported evaluation map. *)

(** 求值恢复运输后的求值映射。 *)

Lemma exp_cmp_eval (X Y : C)
  : eval ∘ (exp_cmp X Y × id) ≈
      fmap F eval ∘ preserved_product_inv F preserves (Y ^ X) X.
Proof. apply exp_β. Qed.

(** Context substitution commutes with transposition through the comparison. *)

(** 经过比较时，上下文替换与转置交换。 *)

Lemma exp_cmp_curry {X Y Z : C} (f : Hom (Z × X) Y)
  : exp_cmp X Y ∘ fmap F (ƛ f)
    ≈ ƛ (fmap F f
      ∘ preserved_product_inv F preserves Z X).
Proof.
  unfold exp_cmp.
  rewrite <- exp_curry_comp_r. apply exp_curry_proper.
  rewrite <- (@fmap_id _ _ _ _ (@isFct C D F) X).
  rewrite comp_assoc, <- preserved_product_inv_natural,
    <- comp_assoc, <- fmap_comp.
  pose proof (@exp_β C PC EC X Y Z f) as Hβ.
  unfold uncurry in Hβ. rewrite Hβ. reflexivity.
Qed.

End ExponentialComparison.

(** ** Composition without Exponential Preservation

    Fix products and exponentials in three categories. Supply only
    binary-product preservation for two functors and their composite;
    the last witness may be [preserved_product_comp] or another one.
    The comparison equation does not assert that any comparison is
    invertible, and needs no terminal objects. *)

(** ** 不依赖指数保持性的复合

    固定三个范畴中的积和指数，只给两个函子及其复合的二元积保持性；最后
    的见证可以是 [preserved_product_comp]，也可以另给。比较方程不声称
    任一比较可逆，也不需要终对象。 *)

Section ExponentialComposition.
Context {C D E : Cat} (F : Fct C D) (G : Fct D E).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}
    `{PE : !HasProduct E} `{EE : !HasExponential PE}.
Context (preservesF : ∀ X Y : C,
    is_product (F X) (F Y) (F (X × Y)) (fmap F π1) (fmap F π2)).
Context (preservesG : ∀ X Y : D,
    is_product (G X) (G Y) (G (X × Y)) (fmap G π1) (fmap G π2)).
Context (preservesGF : ∀ X Y : C,
    is_product ((G ∘F F) X) ((G ∘F F) Y)
      ((G ∘F F) (X × Y))
      (fmap (G ∘F F) π1) (fmap (G ∘F F) π2)).

(** The composite comparison factors through the mapped first comparison
    and the second comparison. All maps retain their original data. *)

(** 复合比较分解为首比较的像与第二个比较；所有映射保留原数据。 *)

Lemma exp_cmp_comp (X Y : C)
  : exp_cmp (G ∘F F) preservesGF X Y ≈
      exp_cmp G preservesG (F X) (F Y) ∘
        fmap G (exp_cmp F preservesF X Y).
Proof.
  apply exp_ext.
  unfold exp_cmp at 1 2.
  rewrite exp_β, exp_uncurry_comp_r, exp_β,
    (preserved_product_inv_comp F G preservesF preservesG preservesGF).
  change (fmap G (fmap F eval) ∘
    (fmap G (preserved_product_inv F preservesF (Y ^ X) X) ∘
      preserved_product_inv G preservesG (F (Y ^ X)) (F X)) ≈
    (fmap G eval ∘
      preserved_product_inv G preservesG (F Y ^ F X) (F X)) ∘
      (fmap G (exp_cmp F preservesF X Y) × id)).
  transitivity (fmap G (fmap F eval ∘
      preserved_product_inv F preservesF (Y ^ X) X) ∘
    preserved_product_inv G preservesG (F (Y ^ X)) (F X)).
  - rewrite fmap_comp, comp_assoc. reflexivity.
  - rewrite <- (exp_cmp_eval F preservesF X Y), fmap_comp,
      !comp_assoc.
    apply comp_proper; [reflexivity |].
    pose proof (preserved_product_inv_natural G preservesG
      (exp_cmp F preservesF X Y)
      (@Cats.Cat.Core.id D (F X))) as H.
    rewrite (@fmap_id _ _ _ _ (@isFct D E G)) in H. exact H.
Defined.

End ExponentialComposition.

(** ** Comparing Exponentials along a Functor

    Fix source terminal and product structures, products in the target, and
    exponentials in both categories. For a cartesian functor [F], construct
    the exponential comparison and its evaluation and currying equations. *)

(** ** 沿函子比较指数对象

    固定来源的终对象与积、目标的积以及两侧的指数结构，为笛卡尔函子 [F] 构造指数比较，并给出求值和柯里化方程。 *)

Section ExponentialComparison.
Context {C D : Cat} (F : Fct C D)
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}
    `{HF : !IsCartF F TC PC}.

(** Transpose the image evaluation after the inverse product comparison. *)

(** 像求值与逆向积比较复合后转置。 *)

Definition fct_exp_cmp (X Y : C)
  : Hom (F (Y ^ X)) (F Y ^ F X)
  := exp_cmp F
    (fct_product (F := F)) X Y.

(** Currying is preserved through the canonical comparisons. *)

(** 柯里化通过规范比较得到保持。 *)

Lemma fct_curry {X Y Z : C} (f : Hom (Z × X) Y)
  : fct_exp_cmp X Y ∘ fmap F (ƛ f) ≈
      ƛ (fmap F f ∘ fct_product_inv F Z X).
Proof. apply exp_cmp_curry. Qed.

(** Evaluation is preserved in the same comparison square. *)

(** 求值在同一比较方形中得到保持。 *)

Lemma fct_eval (X Y : C)
  : eval ∘ (fct_exp_cmp X Y × id) ≈
      fmap F eval ∘ fct_product_inv F (Y ^ X) X.
Proof. apply exp_cmp_eval. Qed.

End ExponentialComparison.
