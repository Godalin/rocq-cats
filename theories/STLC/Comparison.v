From Cats Require Export
  STLC.TypeInterpretation
  STLC.Quotation.
From Cats Require Import
  Cat.Core
  Cat.Morphism
  Cat.Natural
  Cat.Terminal
  Cat.Product.Core
  Cat.Product.Transport
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Cat.Exponential.Transport
  Cat.CCC
  Cat.Functor.Closed.

(** * Comparing Structure-Preserving Interpretations

    A CCC functor is compared with recursive interpretation through canonical
    object isomorphisms, never by equality of functor records. *)

(** * 保持结构解释之间的比较

    以规范对象同构比较 CCC 函子与递归解释，不使用函子记录原生相等。 *)

(** ** Comparing choices through canonical isomorphisms

    Fix a CCC functor [F] out of [TyCat B], an assignment [I] and specified
    base isomorphisms [β]. The comparison at a type has direction
    [TyI I A ≅ F A]. At unit it uses terminal uniqueness; at a product it
    combines the factor comparisons with the functor's product comparison;
    at a function it uses the exponential's contravariant argument action.
    The inverse argument comparison is essential to that last direction.

    Naturality is proved by first evaluating a term in two related
    environments. The induction keeps a map between their source objects,
    so the binding step can use the product and curry comparison laws.
    Literal quotation then yields the natural comparison at every arrow.
    [context_compare_term] records the corresponding equation for a term
    with a packed source. The equational and inhabitation arguments later
    instantiate these same constructions with the identity functor. *)

(** ** 通过规范同构比较不同选择

    固定从 [TyCat B] 出发的 CCC 函子 [F]、赋值 [I] 和指定基类型同构 [β]。
    类型处的比较方向是 [TyI I A ≅ F A]。单位情形使用终对象唯一性；积情形
    结合因子比较与函子的积比较；函数情形使用指数在参数上的反变作用。
    最后一种方向必须使用参数比较的逆。

    自然性先通过两个相关环境中的项求值证明。归纳中保留环境源对象之间的一条
    映射，绑定步骤因而能使用积与 curry 的比较定律。随后借助字面语法还原，
    得到每条箭头处的自然比较。[context_compare_term] 记录了项在打包源上的
    相应方程。等式与可居留性论证都将同一组构造实例化到恒等函子上。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.

Section Comparison.
Universes b e l.
Context {B : Type@{b}} {C : Cat} `{HC : !CCC C}
    (F : Functor (TyCat@{b e l} B) C)
    `{HF : !IsCCCF F (TyCat_CCC B) HC}
    (I : B → @Ob C) (β : ∀ b, I b ≅ F (ty_base b)).

Local Instance source_ccc
  : CCC (TyCat@{b e l} B)
  := TyCat_CCC B.
Local Existing Instance HC.


(** Recursive comparison at types, obtained solely from preservation of
    terminal objects, products and exponentials. *)

(** 类型上的递归比较，仅由终对象、积与指数的保持性导出。 *)

Fixpoint type_compare (A : Ty B)
  : TyI I A ≅ F A
  := match A as A return TyI I A ≅ F A with
  | ty_base b => β b
  | ty_unit => terminal_unique (@terminal_universal C (@hasTerminal C HC))
      (@functor_terminal (TyCat@{b e l} B) C F (TyCat_HasTerminal B)
        (TyCat_HasProduct B) (@isCartesianF _ _ F _ _ HF))
  | ty_prod A U => iso_trans (product_iso (type_compare A) (type_compare U))
      (iso_symm (functor_product_iso F A U))
  | ty_arr A U => iso_trans
      (exponential_iso (type_compare A) (type_compare U))
      (iso_symm (existT _ (functor_exponential_comparison F A U)
        (@functor_exponential _ _ F _ _ HF A U)))
  end.

(** The product component is the canonical inverse comparison after the
    component maps on its factors. *)

(** 积分量是因子分量与规范逆向积比较的复合。 *)

Lemma type_compare_product (A U : Ty B)
  : (type_compare (ty_prod A U)).1 ≈
      functor_product_inv F A U ∘
        ((type_compare A).1 × (type_compare U).1).
Proof. reflexivity. Qed.

(** Both projections commute with the type comparisons. *)

(** 两个投影与类型比较交换。 *)

Lemma type_compare_π1 (A U : Ty B)
  : fmap F (@Cats.Cat.Product.Core.π1 (TyCat@{b e l} B) (TyCat_HasProduct B) A U)
      ∘ (type_compare (ty_prod A U)).1 ≈ (type_compare A).1 ∘ π1.
Proof.
  rewrite type_compare_product, <- comp_assoc,
    (fst (functor_product_inv_β F A U)), cross_η, product_β1.
  reflexivity.
Qed.

(** The second projection has the corresponding comparison equation. *)

(** 第二投影具有相应的比较方程。 *)

Lemma type_compare_π2 (A U : Ty B)
  : fmap F (@Cats.Cat.Product.Core.π2 (TyCat@{b e l} B) (TyCat_HasProduct B) A U)
      ∘ (type_compare (ty_prod A U)).1 ≈ (type_compare U).1 ∘ π2.
Proof.
  rewrite type_compare_product, <- comp_assoc,
    (snd (functor_product_inv_β F A U)), cross_η, product_β2.
  reflexivity.
Qed.

(** The exponential comparison cancels its selected inverse component. *)

(** 指数比较消去所选逆向分量。 *)

Lemma type_compare_function (A U : Ty B)
  : functor_exponential_comparison F A U ∘
      (type_compare (ty_arr A U)).1 ≈
      (exponential_iso (type_compare A) (type_compare U)).1.
Proof.
  change (functor_exponential_comparison F A U ∘
    ((@functor_exponential _ _ F _ _ HF A U).1 ∘
      (exponential_iso (type_compare A) (type_compare U)).1) ≈
    (exponential_iso (type_compare A) (type_compare U)).1).
  rewrite <- comp_assoc, (snd (@functor_exponential _ _ F _ _ HF A U).2),
    comp_id_l. reflexivity.
Qed.

(** Evaluation intertwines the source and target type comparisons. *)

(** 求值使源、目标类型比较相容。 *)

Lemma type_compare_eval (A U : Ty B)
  : fmap F (@Cats.Cat.Exponential.Core.eval (TyCat@{b e l} B) (TyCat_HasProduct B)
      (TyCat_HasExponential B) A U) ∘
      functor_product_inv F (ty_arr A U) A ∘
      ((type_compare (ty_arr A U)).1 × (type_compare A).1) ≈
      (type_compare U).1 ∘ eval.
Proof.
  rewrite <- (@functor_eval (TyCat@{b e l} B) C F
    (TyCat_HasTerminal B) (TyCat_HasProduct B) (TyCat_HasExponential B)
    (@hasProduct C HC) (@hasExponential C HC)
    (@isCartesianF _ _ F _ _ HF) A U), comp_assoc, <- cross_comp,
    type_compare_function, comp_id_l.
  apply exponential_iso_eval.
Qed.

(** The comparison transports transposes when their uncurried maps agree. *)

(** 非转置映射相容时，比较也保持其转置。 *)

Lemma type_compare_curry {Z A U : Ty B} {X : @Ob C}
    (f : (@Hom (TyCat@{b e l} B)) (ty_prod Z A) U)
    (g : Hom (X × TyI I A) (TyI I U)) (z : Hom X (F Z))
    (H : (type_compare U).1 ∘ g ≈ fmap F f ∘
      functor_product_inv F Z A ∘ (z × (type_compare A).1))
  : (type_compare (ty_arr A U)).1 ∘ (ƛ g) ≈
      fmap F (@curry (TyCat@{b e l} B) (TyCat_HasProduct B)
        (TyCat_HasExponential B) A U Z f) ∘ z.
Proof.
  apply (iso_mono (functor_exponential_comparison F A U)
    (@functor_exponential _ _ F _ _ HF A U)).
  rewrite <- !comp_assoc, type_compare_function, functor_curry.
  change (( (type_compare U).1 ^ (type_compare A).2.1)%hom ∘ (ƛ g) ≈
    (ƛ (fmap F f ∘ functor_product_inv F Z A)) ∘ z).
  rewrite <- exponential_curry_dimap, <- exponential_curry_comp_r.
  apply exponential_curry_proper.
  rewrite H, !comp_assoc, <- cross_comp,
    comp_id_r, (snd (type_compare A).2.2). reflexivity.
Qed.

(** An environment comparison extends under binders by the product comparison. *)

(** 环境比较通过积比较扩张到绑定变量之下。 *)

Lemma type_compare_environment {Γ Z X}
    (η : TyEnv (B := B) Z Γ) (ρ : Env I X Γ) (z : Hom X (F Z))
    (H : ∀ A x, (type_compare A).1 ∘ ρ A x ≈ fmap F (η A x) ∘ z)
    (A : Ty B)
  : ∀ U x, (type_compare U).1 ∘ env_lift I ρ U x ≈
      fmap F (ty_env_lift η U x) ∘
        (functor_product_inv F Z A ∘ (z × (type_compare A).1)).
Proof.
  intros U [x | x].
  - unfold env_lift, env_extend, env_comp, ty_env_lift; cbn.
    rewrite <- comp_assoc, (H U x).
    rewrite (@functor_comp (TyCat@{b e l} B) C F
      (ty_prod Z A) Z U (η U x)
      (@Cats.Cat.Product.Core.π1 (TyCat@{b e l} B)
        (TyCat_HasProduct B) Z A)).
    rewrite !comp_assoc.
    rewrite <- (comp_assoc (fmap F (@Cats.Cat.Product.Core.π1
      (TyCat@{b e l} B) (TyCat_HasProduct B) Z A))).
    rewrite (fst (functor_product_inv_β F Z A)), cross_η, product_β1.
    reflexivity.
  - destruct x.
    change ((type_compare A).1 ∘ π2 (X := X) (Y := TyI I A) ≈
      fmap F (@Cats.Cat.Product.Core.π2 (TyCat@{b e l} B)
        (TyCat_HasProduct B) Z A) ∘
      (functor_product_inv F Z A ∘ (z × (type_compare A).1))).
    rewrite <- comp_assoc, (snd (functor_product_inv_β F Z A)),
      cross_η, product_β2. reflexivity.
Qed.

(** Fundamental compatibility: every term commutes with the type and
    environment comparisons. This is proved from CCC preservation alone. *)

(** 基本相容性：每个项均与类型、环境比较交换；证明仅使用 CCC 保持性。 *)

Theorem type_compare_eval_term {Γ A} (t : Tm Γ A)
  : ∀ Z X (η : TyEnv (B := B) Z Γ) (ρ : Env I X Γ)
      (z : Hom X (F Z)),
      (∀ U x, (type_compare U).1 ∘ ρ U x ≈ fmap F (η U x) ∘ z) →
      (type_compare A).1 ∘ tm_eval I t ρ ≈
        fmap F (syntax_eval t η) ∘ z.
Proof.
  induction t; intros Z X η ρ z H; cbn [tm_eval syntax_eval].
  - apply H.
  - destruct (@functor_terminal (TyCat@{b e l} B) C F (TyCat_HasTerminal B)
      (TyCat_HasProduct B) (@isCartesianF _ _ F _ _ HF) X)
      as [h [_ Hu]].
    transitivity h; [apply Hu | symmetry; apply Hu]; constructor.
  - rewrite type_compare_product, comp_assoc.
    rewrite (@product_comp_l C (@hasProduct C HC) _ _ _ _ _
      (tm_eval I t1 ρ) (tm_eval I t2 ρ)
      (type_compare A).1 (type_compare U).1).
    rewrite (IHt1 Z X η ρ z H), (IHt2 Z X η ρ z H).
    rewrite <- (product_comp_r (fmap F (syntax_eval t1 η))
      (fmap F (syntax_eval t2 η)) z), <- comp_assoc.
    rewrite <- (@functor_pair (TyCat@{b e l} B) C F
      (TyCat_HasTerminal B) (TyCat_HasProduct B) (@hasProduct C HC)
      (@isCartesianF _ _ F _ _ HF) A U Z
      (syntax_eval t1 η) (syntax_eval t2 η)).
    reflexivity.
  - rewrite <- comp_assoc, <- type_compare_π1, comp_assoc,
      (IHt Z X η ρ z H), <- comp_assoc, <- functor_comp. reflexivity.
  - rewrite <- comp_assoc, <- type_compare_π2, comp_assoc,
      (IHt Z X η ρ z H), <- comp_assoc, <- functor_comp. reflexivity.
  - apply type_compare_curry.
    rewrite comp_assoc. apply IHt. apply type_compare_environment. exact H.
  - unfold app.
    rewrite <- comp_assoc, <- type_compare_eval, !comp_assoc.
    rewrite (@product_comp_l C (@hasProduct C HC) _ _ _ _ _
      (tm_eval I t1 ρ) (tm_eval I t2 ρ)
      (type_compare (ty_arr A U)).1 (type_compare A).1).
    rewrite (IHt1 Z X η ρ z H), (IHt2 Z X η ρ z H).
    rewrite <- (product_comp_r (fmap F (syntax_eval t1 η))
      (fmap F (syntax_eval t2 η)) z).
    rewrite (@functor_comp (TyCat@{b e l} B) C F
      Z (ty_prod (ty_arr A U) A) U
      (@Cats.Cat.Exponential.Core.eval (TyCat@{b e l} B)
        (TyCat_HasProduct B) (TyCat_HasExponential B) A U)
      (@pair (TyCat@{b e l} B) (TyCat_HasProduct B)
        (ty_arr A U) A Z (syntax_eval t1 η) (syntax_eval t2 η))).
    rewrite (@functor_pair (TyCat@{b e l} B) C F
      (TyCat_HasTerminal B) (TyCat_HasProduct B) (@hasProduct C HC)
      (@isCartesianF _ _ F _ _ HF) (ty_arr A U) A Z
      (syntax_eval t1 η) (syntax_eval t2 η)).
    rewrite !comp_assoc.
    reflexivity.
Qed.

(** Every singleton arrow satisfies the naturality square. *)

(** 每条单变量箭头满足自然性方形。 *)

Theorem type_compare_natural {A U : Ty B}
    (h : (@Hom (TyCat@{b e l} B)) A U)
  : (type_compare U).1 ∘ type_interp I h ≈
      fmap F h ∘ (type_compare A).1.
Proof.
  assert (He : ∀ V x, (type_compare V).1 ∘ single_env I A V x ≈
    fmap F (ty_single_env A V x) ∘ (type_compare A).1).
  { intros V [x | x]; [destruct x | destruct x].
    change ((type_compare A).1 ∘ id ≈
      fmap F (@Cats.Cat.Core.id (TyCat@{b e l} B) A) ∘ (type_compare A).1).
    rewrite functor_id, comp_id_l, comp_id_r. reflexivity. }
  pose proof (type_compare_eval_term (h U var_zero) A (TyI I A)
    (ty_single_env A) (single_env I A) (type_compare A).1 He) as H.
  rewrite syntax_eval_retract in H. exact H.
Qed.

(** The recursively derived type comparisons form a natural transformation. *)

(** 递归导出的类型比较形成自然变换。 *)

Program Definition TypeComparisonN
  : TypeInterpretF I ⇒ F
  :=
  {|nt A := (type_compare A).1
  |}.
Next Obligation. exact (type_compare_natural f). Qed.

(** Any CCC functor with the specified base-type isomorphisms is naturally
    isomorphic to the recursively constructed interpretation. *)

(** 具有指定基类型同构的任意 CCC 函子，都自然同构于递归构造的解释。 *)

Definition type_interpretation_nat_iso
  : TypeInterpretF I ≅N F.
Proof. exists TypeComparisonN. intros A. exact (type_compare A).2. Defined.

(** Compare a nested semantic context with the image of its product type. *)

(** 比较嵌套语义上下文与其积类型的像。 *)

Fixpoint context_compare (Γ : Ctx B)
  : CtxI I Γ ≅ F (CtxTy Γ)
  := match Γ as Γ return CtxI I Γ ≅ F (CtxTy Γ) with
  | ctx_empty => type_compare ty_unit
  | ctx_snoc Γ A => iso_trans
      (product_iso (context_compare Γ) (type_compare A))
      (iso_symm (functor_product_iso F (CtxTy Γ) A))
  end.

(** Context and variable comparisons agree for every projection. *)

(** 上下文比较与变量比较在每个投影上相容。 *)

Lemma context_compare_environment (Γ : Ctx B)
  : ∀ A x, (type_compare A).1 ∘ ctx_env I Γ A x ≈
      fmap F (packed_env@{b e l _} Γ A x) ∘ (context_compare Γ).1.
Proof.
  induction Γ as [|Γ IH A]; intros U x; [destruct x |].
  exact (type_compare_environment (packed_env@{b e l _} Γ) (ctx_env I Γ)
    (context_compare Γ).1 IH A U x).
Qed.

(** Standard context interpretation agrees with quotation through the
    canonical context isomorphism. *)

(** 标准上下文解释通过规范上下文同构与项表示一致。 *)

Theorem context_compare_term {Γ A} (t : Tm Γ A)
  : (type_compare A).1 ∘ tm_interp I t ≈
      fmap F (quote_tm t) ∘ (context_compare Γ).1.
Proof.
  transitivity (fmap F (syntax_eval t (packed_env@{b e l _} Γ)) ∘
    (context_compare Γ).1).
  - apply type_compare_eval_term. apply context_compare_environment.
  - apply comp_proper; [|reflexivity].
    apply functor_fmap_proper. apply syntax_eval_packed.
Qed.

End Comparison.
