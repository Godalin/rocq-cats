From Cats Require Export Cat.Functor.Cartesian.
From Cats Require Import
  Cat.Core
  Cat.Isomorphism
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Cat.CCC.

(** * Cartesian Closed Functors

    Product preservation uses universal properties. Exponential preservation
    asks that its canonical comparison be invertible, not an object equation. *)

(** * 笛卡尔闭函子

    积保持性使用泛性质；指数保持性要求规范比较可逆，不要求对象方程。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.

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

Definition functor_exponential_comparison (X Y : @Ob C)
  : Hom (F ((Y ^ X)%ob)) (F Y ^ F X)
  := ƛ (fmap F eval ∘ functor_product_inv F ((Y ^ X)%ob) X).

(** Currying is preserved through the canonical comparisons. *)

(** 柯里化通过规范比较得到保持。 *)

Lemma functor_curry {X Y Z : @Ob C} (f : Hom (Z × X) Y)
  : functor_exponential_comparison X Y ∘ fmap F (ƛ f) ≈
      ƛ (fmap F f ∘ functor_product_inv F Z X).
Proof.
  unfold functor_exponential_comparison.
  rewrite <- exponential_curry_comp_r. apply exponential_curry_proper.
  rewrite <- (@functor_id C D F X).
  rewrite comp_assoc, <- functor_product_inv_natural,
    <- comp_assoc, <- functor_comp.
  pose proof (@exponential_β C PC EC X Y Z f) as Hβ.
  unfold uncurry in Hβ. rewrite Hβ. reflexivity.
Qed.

(** Evaluation is preserved in the same comparison square. *)

(** 求值在同一比较方形中得到保持。 *)

Lemma functor_eval (X Y : @Ob C)
  : eval ∘ (functor_exponential_comparison X Y × id) ≈
      fmap F eval ∘ functor_product_inv F ((Y ^ X)%ob) X.
Proof. apply exponential_β. Qed.

End ExponentialComparison.

(** A CCC functor preserves finite products and has invertible exponential
    comparisons. All structures are named and explicitly supplied. *)

(** CCC 函子保持有限积，并具有可逆的指数比较；所有结构具名且显式提供。 *)

Class IsCCCF {C D : Cat} (F : Fct C D) (HC : CCC C) (HD : CCC D)
  :=
  { isCartF :: IsCartF F (@hasTerminal C HC) (@hasProduct C HC)
  ; functor_exponential X Y
      : is_iso (@functor_exponential_comparison C D F
          (@hasTerminal C HC) (@hasProduct C HC) (@hasExponential C HC)
          (@hasProduct D HD) (@hasExponential D HD) isCartF X Y)
  }.

(** Identity functors are cartesian closed relative to the same choices. *)

(** 对同一选定结构，恒等函子是笛卡尔闭函子。 *)

Program Definition IdF_IsCCCF (C : Cat) (HC : CCC C)
  : IsCCCF (@IdF C) HC HC
  :=
  {|isCartF := IdF_IsCartF C (@hasTerminal C HC) (@hasProduct C HC)
  |}.
Next Obligation.
  assert (H : functor_exponential_comparison (@IdF C)
    (TC := @hasTerminal C HC) (PC := @hasProduct C HC)
    (EC := @hasExponential C HC) (PD := @hasProduct C HC)
    (ED := @hasExponential C HC)
    (HF := IdF_IsCartF C (@hasTerminal C HC) (@hasProduct C HC))
    X Y ≈ id).
  { unfold functor_exponential_comparison.
    rewrite id_functor_product_inv, comp_id_r.
    apply exponential_curry_eval. }
  exists id. split; unfold is_linv_of, is_rinv_of;
    [rewrite comp_id_l | rewrite comp_id_r]; exact H.
Defined.

(** ** Composition of Cartesian Closed Functors *)

(** ** 笛卡尔闭函子的复合 *)

Section ClosedFunctorComposition.
Context {C D E : Cat} (F : Fct C D) (G : Fct D E)
    (HC : CCC C) (HD : CCC D) (HE : CCC E)
    (HF : IsCCCF F HC HD) (HG : IsCCCF G HD HE).
Local Existing Instance HC.
Local Existing Instance HD.
Local Existing Instance HE.
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
Proof.
  apply exponential_ext.
  unfold functor_exponential_comparison at 1 2.
  rewrite exponential_β, exponential_uncurry_comp_r, exponential_β,
    functor_product_inv_comp.
  change (fmap G (fmap F eval) ∘
    (fmap G (functor_product_inv F ((Y ^ X)%ob) X) ∘
      functor_product_inv G (F ((Y ^ X)%ob)) (F X)) ≈
    (fmap G eval ∘ functor_product_inv G ((F Y ^ F X)%ob) (F X)) ∘
      (fmap G (functor_exponential_comparison F X Y) × id)).
  transitivity (fmap G (fmap F eval ∘ functor_product_inv F ((Y ^ X)%ob) X) ∘
    functor_product_inv G (F ((Y ^ X)%ob)) (F X)).
  - rewrite functor_comp, comp_assoc. reflexivity.
  - rewrite <- (functor_eval F X Y), functor_comp, !comp_assoc.
    apply comp_proper; [reflexivity |].
    pose proof (functor_product_inv_natural G
      (functor_exponential_comparison F X Y)
      (@Cats.Cat.Core.id D (F X))) as H.
    rewrite functor_id in H. exact H.
Qed.

(** Chosen CCC-preservation proofs compose; no global instance is enabled. *)

(** 选定的 CCC 保持证明可以复合，不启用全局实例。 *)

Program Definition CompF_IsCCCF
  : IsCCCF (G ∘F F) HC HE
  :=
  {|isCartF := CompF_IsCartF F G
  |}.
Next Obligation.
  refine (is_iso_equiv (symmetry (functor_exponential_comparison_comp X Y)) _).
  apply is_iso_comp.
  - apply (@functor_is_iso D E G).
    exact (@functor_exponential C D F HC HD HF X Y).
  - exact (@functor_exponential D E G HD HE HG (F X) (F Y)).
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

Class CCCFct {C D : Cat} (HC : CCC C) (HD : CCC D)
  :=
  { CCCF :> @CartFct C D
      (@hasTerminal C HC) (@hasProduct C HC)
  ; ccc_functor_exponential (X Y : @Ob C)
    : is_iso (@functor_exponential_comparison C D CCCF
        (@hasTerminal C HC) (@hasProduct C HC) (@hasExponential C HC)
        (@hasProduct D HD) (@hasExponential D HD)
        (cartesian_isCartF CCCF) X Y)
  }.

Arguments CCCF {_ _ _ _} _.
Arguments ccc_functor_exponential {_ _ _ _} _ _ _.

(** Recover the fixed-functor presentation from the stored data. This
    generic inherited instance needs an explicit bundled functor; it does
    not choose a concrete model. Cartesian evidence is shared definitionally. *)

(** 从保存的数据恢复固定函子呈现。这个通用继承实例需要显式的打包函子，
    不选取具体模型；笛卡尔证据在定义上共享。 *)

Program Instance CCCFct_IsCCCF {C D : Cat} {HC : CCC C} {HD : CCC D}
    (F : CCCFct HC HD)
  : IsCCCF F HC HD
  :=
  {|isCartF := cartesian_isCartF (CCCF F)
  ; functor_exponential := ccc_functor_exponential F
  |}.

(** Bundle existing CCC-preservation evidence without changing the
    underlying functor, its product mediators or its exponential inverses. *)

(** 打包已有 CCC 保持性证据，不改变底层函子、积中介或指数比较的逆。 *)

Program Definition CCCFctFromPreservation {C D : Cat}
    {HC : CCC C} {HD : CCC D} (F : Fct C D) (HF : IsCCCF F HC HD)
  : CCCFct HC HD
  :=
  {|CCCF := CartFctFromPreservation F (@isCartF _ _ F HC HD HF)
  ; ccc_functor_exponential := @functor_exponential _ _ F HC HD HF
  |}.

(** The bundled identity uses the existing CCC-preservation theorem. *)

(** 打包的恒等函子使用已有 CCC 保持性定理。 *)

Program Definition IdCCCF (C : Cat) (HC : CCC C)
  : CCCFct HC HC
  := CCCFctFromPreservation IdF (IdF_IsCCCF C HC).

(** Compose bundled CCC functors using the established comparison and
    preservation proofs; the underlying functor is ordinary composition. *)

(** 用已确立的比较及保持性证明复合打包 CCC 函子；底层函子仍为普通复合。 *)

Program Definition CompCCCF {C D E : Cat}
    {HC : CCC C} {HD : CCC D} {HE : CCC E}
    (G : CCCFct HD HE) (F : CCCFct HC HD)
  : CCCFct HC HE
  := CCCFctFromPreservation (G ∘F F)
      (CompF_IsCCCF F G HC HD HE
        (CCCFct_IsCCCF F) (CCCFct_IsCCCF G)).
