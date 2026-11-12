From Cats Require Export
  STLC.Equational
  STLC.ContextEquivalence.
From Cats Require Import
  Cat.Core
  Cat.Morphism
  Cat.Natural
  Cat.Terminal
  Cat.Product.Core
  Cat.Product.Transport
  Cat.Exponential.Core
  Cat.Exponential.Transport
  Cat.CCC
  Cat.Functor.Closed.

(** * The Free Cartesian Closed Universal Property

    A base-type assignment extends to a CCC functor. A specified comparison
    at base types extends to a unique natural transformation, and the
    canonical extension is invertible. Only transformations, not their
    naturality or inverse-law proofs, are compared. *)

(** * 自由笛卡尔闭泛性质

    基类型赋值扩张为 CCC 函子。基类型处指定的比较扩张为唯一自然变换，规范扩张
    可逆。仅比较变换分量，不比较自然性或互逆律的证明。 *)

(** ** Interpreting the whole language canonically

    The free property fixes [C], its chosen CCC structure, a base assignment
    [I], a CCC-preserving functor [F] and isomorphisms from [I] to the base
    images of [F]. [type_interpretation_universal] returns the canonical
    natural isomorphism and a uniqueness witness for natural transformations
    extending those same base components. The choices in this statement
    matter: it does not assert that all interpretations are equal outright.

    For uniqueness, unit uses terminality, products use naturality at the
    projections, and function types use naturality at evaluation plus
    invertible exponential comparisons. Induction on types forces each
    component. Naturality itself supplies the needed compatibility; the
    candidate transformations need no extra structure-preservation fields.
    This universal property complements model completeness, which tests
    particular equations rather than whole interpretation functors. *)

(** ** 规范地解释整个语言

    自由性质固定 [C]、其选定 CCC 结构、基类型赋值 [I]、保持 CCC 结构的函子
    [F]，以及从 [I] 到 [F] 的基类型像的同构。
    [type_interpretation_universal] 返回规范自然同构，并为扩张同样基类型分量
    的自然变换给出唯一性见证。这些固定选择属于陈述的一部分，并不断言所有
    解释直接相等。

    唯一性的单位情形使用终对象性质，积情形使用投影处的自然性，函数情形使用
    求值处的自然性与可逆指数比较。对类型归纳便确定每个分量。自然性本身提供
    需要的相容性，候选变换无须附加保持结构的字段。这个泛性质补充模型完备性；
    后者检验具体等式，而非整个解释函子。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.

(** ** The Universal Property of the Syntactic CCC

    Fix a CCC model, a CCC functor [F] from syntax and chosen base comparisons
    [β]. Prove the induced interpretation comparison is the unique compatible
    natural transformation. *)

(** ** 语法 CCC 的泛性质

    固定 CCC 模型、从语法出发的 CCC 函子 [F] 及选定基类型比较 [β]，证明诱导的解释比较是唯一相容的自然变换。 *)

Section FreeCCC.
Universes b e l.
Context {B : Type@{b}} {C : Cat} `{HC : !CCC C}
    (F : Functor (TyCat@{b e l} B) C)
    `{HF : !IsCCCF F (TyCat_CCC B) HC}
    (I : B → @Ob C) (β : ∀ b, I b ≅ F (ty_base b)).
Local Instance source_ccc
  : CCC (TyCat@{b e l} B)
  := TyCat_CCC B.
Local Existing Instance HC.

(** Naturality at both projections determines a transformation on products. *)

(** 两个投影处的自然性确定变换在积上的分量。 *)

Lemma type_natural_product (α : TypeInterpretF I ⇒ F) (X Y : Ty B)
  : α (ty_prod X Y) ≈ functor_product_inv F X Y ∘ (α X × α Y).
Proof.
  apply (product_cone_ext (@functor_product (TyCat@{b e l} B) C F
    (TyCat_HasTerminal B) (TyCat_HasProduct B)
    (@isCartesianF _ _ F _ _ HF) X Y)).
  - rewrite <- (nt_naturality α (@Cats.Cat.Product.Core.π1
      (TyCat@{b e l} B) (TyCat_HasProduct B) X Y)).
    rewrite <- comp_assoc, (fst (functor_product_inv_β F X Y)),
      cross_η, product_β1.
    apply comp_proper; [reflexivity |]. exact (type_interp_π1 I X Y).
  - rewrite <- (nt_naturality α (@Cats.Cat.Product.Core.π2
      (TyCat@{b e l} B) (TyCat_HasProduct B) X Y)).
    rewrite <- comp_assoc, (snd (functor_product_inv_β F X Y)),
      cross_η, product_β2.
    apply comp_proper; [reflexivity |]. exact (type_interp_π2 I X Y).
Qed.

(** A transformation also intertwines evaluation through its product square. *)

(** 变换也通过积比较方形使求值相容。 *)

Lemma type_natural_eval (α : TypeInterpretF I ⇒ F) (A U : Ty B)
  : fmap F (@Cats.Cat.Exponential.Core.eval (TyCat@{b e l} B)
      (TyCat_HasProduct B) (TyCat_HasExponential B) A U) ∘
      functor_product_inv F (ty_arr A U) A ∘
      (α (ty_arr A U) × α A) ≈ α U ∘ eval.
Proof.
  rewrite comp_assoc, <- type_natural_product.
  rewrite <- (nt_naturality α (@Cats.Cat.Exponential.Core.eval
    (TyCat@{b e l} B) (TyCat_HasProduct B) (TyCat_HasExponential B) A U)).
  apply comp_proper; [reflexivity |]. exact (type_interp_eval I A U).
Qed.

(** The image evaluation detects arrows when the canonical exponential
    comparison is invertible and the argument comparison is an isomorphism. *)

(** 规范指数比较可逆且参数比较为同构时，像求值可检测箭头相等。 *)

Lemma type_functor_exponential_ext {A U : Ty B} {Z : @Ob C}
    {f g : Hom Z (F (ty_arr A U))}
    (H : fmap F (@Cats.Cat.Exponential.Core.eval (TyCat@{b e l} B)
      (TyCat_HasProduct B) (TyCat_HasExponential B) A U) ∘
      functor_product_inv F (ty_arr A U) A ∘
      (f × (type_compare F I β A).1) ≈
      fmap F (@Cats.Cat.Exponential.Core.eval (TyCat@{b e l} B)
        (TyCat_HasProduct B) (TyCat_HasExponential B) A U) ∘
      functor_product_inv F (ty_arr A U) A ∘
      (g × (type_compare F I β A).1))
  : f ≈ g.
Proof.
  pose proof (@functor_eval (TyCat@{b e l} B) C F
    (TyCat_HasTerminal B) (TyCat_HasProduct B) (TyCat_HasExponential B)
    (@hasProduct C HC) (@hasExponential C HC)
    (@isCartesianF _ _ F _ _ HF) A U) as Ev.
  apply (iso_mono (functor_exponential_comparison F A U)
    (@functor_exponential _ _ F _ _ HF A U)).
  apply (exponential_ext_iso (type_compare F I β A)).
  transitivity ((eval ∘ (functor_exponential_comparison F A U × id)) ∘
    (f × (type_compare F I β A).1)).
  - rewrite comp_assoc, <- cross_comp, comp_id_l. reflexivity.
  - rewrite Ev, H, <- Ev,
      comp_assoc, <- cross_comp, comp_id_l. reflexivity.
Qed.

(** ** Why naturality determines the extension

    For products, naturality at the two projections fixes both components;
    product uniqueness fixes the whole arrow. For function types, naturality
    at evaluation fixes the behavior after an argument is supplied.
    [type_functor_exponential_ext] detects equality from that behavior,
    using the invertible argument comparison. The terminal case has only
    one arrow. These three facts make induction on types possible.

    The conclusion concerns every natural transformation with the specified
    base components. It does not first assume that the transformation
    preserves the chosen CCC operations: naturality already forces the
    needed equations. Uniqueness is pointwise hom equality, so neither
    naturality proofs nor functor records need be equal. *)

(** ** 为什么自然性确定扩张

    对积，两个投影处的自然性固定两个分量，再由积唯一性固定整条箭头。对函数
    类型，求值处的自然性固定提供参数之后的行为；
    [type_functor_exponential_ext] 借助可逆的参数比较，从该行为检测相等。
    终对象情形只有一条箭头。这三点使对类型的归纳成为可能。

    结论覆盖全部具有指定基类型分量的自然变换，无须预先假设变换保持选定 CCC
    操作，自然性已经强制所需方程。唯一性是逐点 Hom 相等，因此不需要自然性
    证明相等，也不需要函子记录相等。 *)

(** Every natural transformation extending the specified base comparison is
    the canonical one. Product and evaluation naturality force all components. *)

(** 扩张指定基类型比较的每个自然变换都等于规范变换；积与求值的自然性确定
    全部类型分量。 *)

Theorem type_comparison_unique (α : TypeInterpretF I ⇒ F)
    (Hbase : ∀ b, α (ty_base b) ≈ (β b).1)
  : α ≈N TypeComparisonN F I β.
Proof.
  intros A. induction A as [b0 | | A IH1 U IH2 | A IH1 U IH2].
  - exact (Hbase b0).
  - destruct (@functor_terminal (TyCat@{b e l} B) C F
      (TyCat_HasTerminal B) (TyCat_HasProduct B)
      (@isCartesianF _ _ F _ _ HF) (TyI I ty_unit)) as [h [_ Hu]].
    transitivity h; [apply Hu | symmetry; apply Hu]; constructor.
  - change (α (ty_prod A U) ≈ (type_compare F I β (ty_prod A U)).1).
    rewrite type_natural_product, type_compare_product.
    apply comp_proper; [reflexivity |]. apply cross_proper; assumption.
  - change (α (ty_arr A U) ≈ (type_compare F I β (ty_arr A U)).1).
    apply type_functor_exponential_ext.
    rewrite <- IH1, (type_natural_eval α A U), IH2, IH1.
    symmetry. apply type_compare_eval.
Qed.

(** The full chosen extension property: the comparison is an isomorphism and
    is unique among all natural transformations with the required base action. *)

(** 完整的选定扩张性质：比较为同构，并在具有指定基类型作用的全部自然变换中
    唯一。 *)

Definition type_interpretation_universal
  : ∃ α : TypeInterpretF I ≅N F,
      is_unique (λ η : TypeInterpretF I ⇒ F,
        ∀ b, η (ty_base b) ≈ (β b).1) α.1.
Proof.
  exists (type_interpretation_nat_iso F I β).
  refine {|this := _
         ; that := _
         |}.
  - intros b0. reflexivity.
  - intros η Hη. apply type_comparison_unique. exact Hη.
Defined.

End FreeCCC.
