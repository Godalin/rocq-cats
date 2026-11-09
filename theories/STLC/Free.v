From Cats Require Export
  STLC.Equational.Core
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

Local Open Scope hom_scope.
Local Open Scope cat_scope.

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
