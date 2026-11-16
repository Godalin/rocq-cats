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

(** A CCC functor preserves finite products and has invertible exponential
    comparisons. All structures are named and explicitly supplied. *)

(** CCC 函子保持有限积，并具有可逆的指数比较；所有结构具名且显式提供。 *)

Class IsCCCF {C D : CCC} (F : Fct C D)
  :=
  { isCartF :: IsCartF F (hasTerminal C) (hasProduct C)
  ; functor_exponential X Y
    : is_iso (@functor_exponential_comparison C D F
        (hasTerminal C) (hasProduct C)
        (hasExponential C)
        (hasProduct D) (hasExponential D) isCartF X Y)
  }.

(** Identity functors are cartesian closed relative to the same choices. *)

(** 对同一选定结构，恒等函子是笛卡尔闭函子。 *)

Program Definition IdF_IsCCCF (C : CCC)
  : @IsCCCF C C (@IdF C)
  :=
  {|isCartF := IdF_IsCartF C (hasTerminal C) (hasProduct C)
  |}.
Next Obligation.
  assert (H : functor_exponential_comparison (@IdF C)
    (TC := hasTerminal C) (PC := hasProduct C)
    (EC := hasExponential C) (PD := hasProduct C)
    (ED := hasExponential C)
    (HF := IdF_IsCartF C (hasTerminal C) (hasProduct C))
    X Y ≈ id).
  { pose proof (id_functor_product_inv C (hasTerminal C) (hasProduct C)
      ((Y ^ X)%ob) X) as HP.
    unfold functor_product_inv in HP.
    unfold functor_exponential_comparison, preserved_exponential_comparison.
    rewrite HP, comp_id_r. apply exponential_curry_eval. }
  exists id. split; unfold is_linv_of, is_rinv_of;
    [rewrite comp_id_l | rewrite comp_id_r]; exact H.
Defined.

(** ** Composition of Cartesian Closed Functors *)

(** ** 笛卡尔闭函子的复合 *)

Section ClosedFunctorComposition.
Context {C D E : CCC} (F : Fct C D) (G : Fct D E)
    (HF : @IsCCCF C D F) (HG : @IsCCCF D E G).
Local Existing Instance HF.
Local Existing Instance HG.

(** The canonical comparison of a composite is the composite of the
    canonical comparisons, under specified hom equality. *)

(** 复合函子的规范比较在指定 Hom 相等下为规范比较的复合。 *)

Lemma functor_exponential_comparison_comp (X Y : @Ob C)
  : functor_exponential_comparison (G ∘F F)
      (HF := CompF_IsCartF F G) X Y ≈
      functor_exponential_comparison G (F X) (F Y) ∘
        fmap G (functor_exponential_comparison F X Y).
Proof. apply preserved_exponential_comparison_comp. Qed.

(** Chosen CCC-preservation proofs compose; no global instance is enabled. *)

(** 选定的 CCC 保持证明可以复合，不启用全局实例。 *)

Program Definition CompF_IsCCCF
  : @IsCCCF C E (G ∘F F)
  :=
  {|isCartF := CompF_IsCartF F G
  |}.
Next Obligation.
  refine (is_iso_equiv (symmetry (functor_exponential_comparison_comp X Y)) _).
  apply is_iso_comp.
  - apply (@functor_is_iso D E G).
    exact (@functor_exponential C D F HF X Y).
  - exact (@functor_exponential D E G HG (F X) (F Y)).
Defined.

End ClosedFunctorComposition.

(** ** Bundled Cartesian Closed Functors *)

(** ** 打包的笛卡尔闭函子 *)

(** A CCC functor extends one cartesian functor with invertibility of the
    canonical exponential comparison. The coercion chain passes through
    [CartFct] to [Fct], storing neither a second functor nor
    another choice of cartesian preservation witnesses. *)

(** CCC 函子为一个笛卡尔函子增加规范指数比较的可逆性；强制转换经
    [CartFct] 到达 [Fct]，不另存函子或另一份笛卡尔保持性见证。 *)

Class CCCFct (C D : CCC)
  :=
  { CCCF :> @CartFct C D
      (hasTerminal C) (hasProduct C)
  ; ccc_functor_exponential (X Y : @Ob C)
    : is_iso (@functor_exponential_comparison C D CCCF
        (hasTerminal C) (hasProduct C) (hasExponential C)
        (hasProduct D) (hasExponential D)
        (cartesian_isCartF CCCF) X Y)
  }.

Arguments CCCF {_ _} _.
Arguments ccc_functor_exponential {_ _} _ _ _.

(** Recover the fixed-functor presentation from the stored data. This
    generic inherited instance needs an explicit bundled functor; it does
    not choose a concrete model. Cartesian evidence is shared definitionally. *)

(** 从保存的数据恢复固定函子呈现。这个通用继承实例需要显式的打包函子，
    不选取具体模型；笛卡尔证据在定义上共享。 *)

Program Instance CCCFct_IsCCCF {C D : CCC}
    (F : CCCFct C D)
  : @IsCCCF C D F
  :=
  {|isCartF := cartesian_isCartF (CCCF F)
  ; functor_exponential := ccc_functor_exponential F
  |}.

(** Bundle existing CCC-preservation evidence without changing the
    underlying functor, its product mediators or its exponential inverses. *)

(** 打包已有 CCC 保持性证据，不改变底层函子、积中介或指数比较的逆。 *)

Program Definition CCCFctFromPreservation {C D : CCC}
    (F : Fct C D) (HF : @IsCCCF C D F)
  : CCCFct C D
  :=
  {|CCCF := CartFctFromPreservation F (@isCartF C D F HF)
  ; ccc_functor_exponential := @functor_exponential C D F HF
  |}.

(** The bundled identity uses the existing CCC-preservation theorem. *)

(** 打包的恒等函子使用已有 CCC 保持性定理。 *)

Program Definition IdCCCF (C : CCC)
  : CCCFct C C
  := CCCFctFromPreservation IdF (IdF_IsCCCF C).

(** Compose bundled CCC functors using the established comparison and
    preservation proofs; the underlying functor is ordinary composition. *)

(** 用已确立的比较及保持性证明复合打包 CCC 函子；底层函子仍为普通复合。 *)

Program Definition CompCCCF {C D E : CCC}
    (G : CCCFct D E) (F : CCCFct C D)
  : CCCFct C E
  := CCCFctFromPreservation (G ∘F F)
      (CompF_IsCCCF F G
        (CCCFct_IsCCCF F) (CCCFct_IsCCCF G)).
