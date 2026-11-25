From Cats Require Export
  Cat.Functor.Cartesian
  Cat.Functor.ExponentialComparison.
From Cats Require Import
  Cat.Core
  Cat.Isomorphism
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Cat.CCC.Core
  Cat.Functor.ExponentialComparison.

(** * Cartesian Closed Functors

    Product preservation uses universal properties. Exponential preservation
    asks that its canonical comparison be invertible, not an object equation.
    Evaluation and currying reuse [Cat.Functor.ExponentialComparison]; that
    weaker interface also applies without terminal preservation. *)

(** * 笛卡尔闭函子

    积保持性使用泛性质；指数保持性要求规范比较可逆，不要求对象方程。
    求值与柯里化复用 [Cat.Functor.ExponentialComparison]，其较弱接口也适用于
    不保持终对象的函子。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.
Local Open Scope ob_scope.

(** Invertibility of the exponential comparison uses the specified
    finite-product preservation witness. *)

(** 指数比较的可逆性使用给定的有限积保持性见证。 *)

Minks.Mixin PreservesExp {C D : CCC} (F : Fct C D)
  extends @IsCartF C D F _ _
  :=
  { fct_exp (X Y : C)
    : is_iso (fct_exp_cmp F (PD := hasProduct D) X Y)
  }.

(** Pack the functor with its two preservation witnesses. Fixing the
    underlying functor gives the relative interface [IsCCCF]. *)

(** 打包函子及其两份保持性见证。固定底层函子即得相对接口 [IsCCCF]。 *)

Minks.Struct CCCFct (C D : CCC)
  extends @CartFct C D _ _
  with  preservesExp
        : PreservesExp [C, D, carrier, isCartF]
  exports IsCCCF [carrier].

Arguments IsCCCF {_ _} _.
Arguments IsCCCF_isCartF {_ _ _} _.
Arguments IsCCCF_preservesExp {_ _ _} _.
Arguments MakeCCCFct {_ _} _ _ _.
Arguments CCCFctOfCartFct {_ _} _ _.
Arguments CCCFctToCartFct {_ _} _.
Arguments CCCFct_preservesExp {_ _} _.
Arguments CCCFctToIsCCCF {_ _} _.
Arguments CCCFctOfIsCCCF {_ _} _ _.

(** Identity functors are cartesian closed relative to the same choices. *)

(** 对同一选定结构，恒等函子是笛卡尔闭函子。 *)

Program Definition IdF_IsCCCF (C : CCC)
  : @IsCCCF C C (@IdF C)
  :=
  {|IsCCCF_isCartF := IdF_IsCartF C _ _
  ; IsCCCF_preservesExp := {|fct_exp := _|}
  |}.
Next Obligation.
  refine (is_iso_equiv (f := id) _ iso_refl.2).
  symmetry. unfold fct_exp_cmp, exp_cmp.
  pose proof (id_fct_product_inv C _ _ (Y ^ X) X) as HP.
  unfold fct_product_inv in HP.
  rewrite HP, comp_id_r. apply exp_curry_eval.
Defined.

(** ** Composition of Cartesian Closed Functors *)

(** ** 笛卡尔闭函子的复合 *)

Section ClosedFunctorComposition.
Context {C D E : CCC} (F : Fct C D) (G : Fct D E)
    `{HF : !IsCCCF F} `{HG : !IsCCCF G}.

(** The canonical comparison of a composite is the composite of the
    canonical comparisons, under specified hom equality. *)

(** 复合函子的规范比较在指定 Hom 相等下为规范比较的复合。 *)

Lemma fct_exp_cmp_comp (X Y : @Ob C)
  : fct_exp_cmp (G ∘F F)
      (HF := CompF_IsCartF F G) X Y ≈
      fct_exp_cmp G (F X) (F Y) ∘
        fmap G (fct_exp_cmp F X Y).
Proof. apply exp_cmp_comp. Qed.

(** Chosen CCC-preservation proofs compose; no global instance is enabled. *)

(** 选定的 CCC 保持证明可以复合，不启用全局实例。 *)

Program Definition CompF_IsCCCF
  : @IsCCCF C E (G ∘F F)
  :=
  {|IsCCCF_isCartF := CompF_IsCartF F G
  ; IsCCCF_preservesExp := {|fct_exp := _|}
  |}.
Next Obligation.
  refine (is_iso_equiv (symmetry (fct_exp_cmp_comp X Y)) _).
  apply is_iso_comp.
  - apply (@fct_is_iso D E G).
    exact (fct_exp (PreservesExp := IsCCCF_preservesExp HF) X Y).
  - exact (fct_exp (PreservesExp := IsCCCF_preservesExp HG) (F X) (F Y)).
Defined.

End ClosedFunctorComposition.

(** ** Bundled Cartesian Closed Functors *)

(** ** 打包的笛卡尔闭函子 *)

(** The bundled identity uses the existing CCC-preservation theorem. *)

(** 打包的恒等函子使用已有 CCC 保持性定理。 *)

Canonical IdCCCF (C : CCC)
  : CCCFct C C
  := CCCFctOfIsCCCF IdF (IdF_IsCCCF C).

(** Compose bundled CCC functors using the established comparison and
    preservation proofs; the underlying functor is ordinary composition. *)

(** 用已确立的比较及保持性证明复合打包 CCC 函子；底层函子仍为普通复合。 *)

Canonical CompCCCF {C D E : CCC}
    (G : CCCFct D E) (F : CCCFct C D)
  : CCCFct C E
  := CCCFctOfIsCCCF (G ∘F F) (CompF_IsCCCF F G).
