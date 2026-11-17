From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.ProductPullback
  Cat.Exponential.Core
  Cat.Pullback
  Cat.Morphism
  Cat.SubobjectIntersection
  Topos.Sub
  Topos.Representation
  Topos.Conjunction
  Topos.PredicateOrder.

(** * Universal Quantification Along Projections

    Classify the name of the constantly true predicate. Exponential
    transposition gives its truth and substitution laws; the product
    pullback square transfers these to a Type-valued predicate adjunction. *)

(** * 沿投影的全称量化

    分类恒真谓词的名称。指数转置给出其为真及代入定律；积的拉回方形将这些
    定律传到 Type 值谓词伴随。 *)

(** Name the true predicate on the bound object using the chosen
    products and exponentials. *)

(** 使用选定积及指数，给出约束对象上恒真谓词的名称。 *)

Definition ForallTruth {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (A : C)
  : Hom 1 (Ω ^ A)
  := ƛ (truth ∘ !).

(** Classifying this global name gives the universal-quantifier arrow. *)

(** 分类该全局名称，得到全称量词箭头。 *)

Definition Forall {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (A : C)
  : Hom (Ω ^ A) Ω
  := χ (Mono_term (ForallTruth A)).

(** Quantify the second factor of a predicate over a product context. *)

(** 对积上下文上谓词的第二因子作全称量化。 *)

Definition forall_predicate {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (A : C) {X : C} (f : Hom (X × A) Ω)
  : Hom X Ω
  := Forall A ∘ (ƛ f).

Notation "'∀Ω[' A ']' f" := (forall_predicate A f)
  (at level 35, f at next level) : hom_scope.

(** ** Truth and Context Substitution

    Fix named terminal, classifier, product and exponential choices.
    Pullbacks and additional topos properties are unnecessary for these
    quantifier arrows, truth criteria and context-substitution laws. *)

(** ** 真与上下文代入

    固定具名终对象、分类子、积及指数选择。量词箭头、为真判据与上下文代入
    定律不需要拉回或额外拓扑斯性质。 *)

Section Forall.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasExponential HP}.

(** Quantification respects the predicate's specified equality. *)

(** 全称量化保持谓词的指定相等。 *)

Global Instance forall_predicate_proper (A X : C)
  : Proper (@HomEq[X × A, Ω] ==> @HomEq[X, Ω]) (forall_predicate A).
Proof.
  intros f g H. unfold forall_predicate. rewrite H. reflexivity.
Qed.

(** The transpose of constant truth is the same global name in every
    context, by the existing currying-substitution law. *)

(** 由已有柯里化代入律，恒真的转置在每个上下文中都是同一全局名称。 *)

Theorem forall_truth_curry (A X : C)
  : (ƛ (truth ∘ ! : Hom (X × A) Ω)) ≈ ForallTruth A ∘ !.
Proof.
  unfold ForallTruth. rewrite <- exp_curry_comp_r.
  apply exp_curry_proper.
  rewrite comp_assoc, (term_η (! ∘ (! × id))). reflexivity.
Qed.

(** Substituting the context commutes with quantifying the unchanged
    bound object. This is the projection substitution square. *)

(** 上下文代入与对未改变的约束对象作全称量化相容，给出投影的代入方形。 *)

Theorem forall_predicate_comp (A : C) {X Y : C}
    (f : Hom (Y × A) Ω) (k : Hom X Y)
  : (∀Ω[A] f) ∘ k ≈ ∀Ω[A] (f ∘ (k × id)).
Proof.
  unfold forall_predicate.
  rewrite comp_assoc, exp_curry_comp_r. reflexivity.
Qed.

(** Universal quantification is true precisely when the original
    predicate is constantly true. No global points are tested. *)

(** 全称量化为真，当且仅当原谓词恒真；不通过测试全局点来定义。 *)

Definition forall_predicate_true (A : C) {X : C} (f : Hom (X × A) Ω)
  : ∀Ω[A] f ≈ truth ∘ ! ↔ f ≈ truth ∘ !.
Proof.
  pose (F := classifier_char_factor (Mono_term (ForallTruth A)) (ƛ f)).
  split.
  - intros H. destruct (fst F H) as [k Hk].
    apply (fst (exp_curry_eq_iff f (truth ∘ !))).
    transitivity (ForallTruth A ∘ (! : Hom X 1)).
    + rewrite Hk, (term_η k). reflexivity.
    + symmetry. apply forall_truth_curry.
  - intros H. apply (snd F). exists !.
    rewrite <- forall_truth_curry, H. reflexivity.
Defined.

End Forall.

(** ** Quantification as a Predicate Right Adjoint

    Add named pullbacks for classified subobjects. The explicit product
    square compares the selected truth inverse image after projection
    substitution with the displayed product subobject. Its factors yield
    the right adjunction, evaluation and monotonicity. *)

(** ** 全称量化为谓词的右伴随

    为分类子对象增加具名拉回。显式积方形将沿投影代入后的选定真逆像与展示的
    积子对象比较，其因子给出右伴随、求值与单调性。 *)

Section ForallOrder.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Projection substitution classifies the product with the bound object,
    preserving transparent comparison factors. *)

(** 沿投影的代入分类与约束对象的积，保留透明比较因子。 *)

Definition classified_product_sub (A : C) {X : C} (r : Hom X Ω)
  : ClassifiedSub (r ∘ (π1 : Hom (X × A) X))
      ~Sub SubProduct (ClassifiedSub r) A.
Proof.
  apply (snd (classifier_char_subobject_eq _ _)).
  rewrite classified_sub_char. symmetry.
  transitivity (χ (sub_mono _ (ClassifiedSub r))
    ∘ (π1 : Hom (X × A) X)).
  - exact (classifier_char_pullback π1 (sub_mono _ (ClassifiedSub r))
      (sub_mono _ (SubProduct (ClassifiedSub r) A)) π1
      (product_projection_pullback (ClassifiedSub r) A)).
  - rewrite classified_sub_char. reflexivity.
Defined.

(** Entailment after weakening is truth on the product of the
    antecedent's chosen subobject with the bound object. *)

(** 弱化后的蕴含，等价于在前件选定子对象与约束对象的积上为真。 *)

Definition predicate_le_product (A : C) {X : C}
    (r : Hom X Ω) (f : Hom (X × A) Ω)
  : r ∘ π1 ⊢Ω f ↔ f ∘ (ClassifiedSub r × id) ≈ truth ∘ !.
Proof.
  pose (E := classified_product_sub A r).
  pose (F := classifier_char_factor (sub_mono _ (ClassifiedSub f))
    (SubProduct (ClassifiedSub r) A)). split.
  - intros H. pose (K := snd F (sub_factor_comp (snd E) H)).
    rewrite classified_sub_char in K. exact K.
  - intros H. apply (sub_factor_comp (fst E)). apply (fst F).
    rewrite classified_sub_char. exact H.
Defined.

(** Quantification is right adjoint to projection substitution. Both
    directions retain actual entailment factors. *)

(** 全称量化是沿投影代入的右伴随，两个方向均保留实际蕴含因子。 *)

Definition predicate_forall_universal (A : C) {X : C}
    (r : Hom X Ω) (f : Hom (X × A) Ω)
  : r ∘ π1 ⊢Ω f ↔ r ⊢Ω ∀Ω[A] f.
Proof.
  pose (P := predicate_le_product A r f).
  pose (T := predicate_le_truth r (∀Ω[A] f)).
  pose (F := forall_predicate_true A (f ∘ (ClassifiedSub r × id))). split.
  - intros H. apply (snd T). rewrite forall_predicate_comp.
    exact (snd F (fst P H)).
  - intros H. apply (snd P). apply (fst F).
    pose (K := fst T H). rewrite forall_predicate_comp in K. exact K.
Defined.

(** A quantified predicate entails its body after projection weakening. *)

(** 全称量化后的谓词沿投影弱化后，蕴含其主体。 *)

Definition predicate_forall_eval (A : C) {X : C} (f : Hom (X × A) Ω)
  : (∀Ω[A] f) ∘ π1 ⊢Ω f
  := snd (predicate_forall_universal A (∀Ω[A] f) f)
      (predicate_le_refl (∀Ω[A] f)).

(** Quantification transports entailment through the same right adjoint. *)

(** 全称量化通过同一右伴随运输蕴含。 *)

Definition predicate_forall_mono (A : C) {X : C}
    {f g : Hom (X × A) Ω} (H : f ⊢Ω g)
  : ∀Ω[A] f ⊢Ω ∀Ω[A] g
  := fst (predicate_forall_universal A (∀Ω[A] f) g)
      (predicate_le_trans (predicate_forall_eval A f) H).

(** Instantiate the bound variable by a term in the same context. *)

(** 用同一上下文中的项实例化约束变量。 *)

Definition predicate_forall_instantiate (A : C) {X : C}
    (f : Hom (X × A) Ω) (a : Hom X A)
  : ∀Ω[A] f ⊢Ω f ∘ ⟨id, a⟩.
Proof.
  pose (H := predicate_le_subst ⟨id, a⟩ (predicate_forall_eval A f)).
  assert (E : ((∀Ω[A] f) ∘ π1) ∘ ⟨id, a⟩ ≈ ∀Ω[A] f).
  { rewrite comp_assoc, product_β1, comp_id_r. reflexivity. }
  exact (sub_factor_comp (snd (classified_sub_congr E)) H).
Defined.

End ForallOrder.
