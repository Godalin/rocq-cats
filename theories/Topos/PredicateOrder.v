From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Pullback
  Cat.Morphism
  Cat.Preorder
  Cat.SubobjectIntersection
  Instance.Set.Subobject
  Instance.Set.SubobjectIntersection
  Topos.Sub
  Topos.Representation
  Topos.Conjunction.

(** * The Type-Valued Entailment Order

    Predicates entail one another by actual factors between their
    classified subobjects. Pull back the existing subobject preorder;
    retain its computational witnesses and use hom equality for mutual
    entailment. No quotient of predicates is required. *)

(** * Type 值蕴含序

    谓词间的蕴含由其分类子对象之间的实际分解因子给出。拉回既有子对象预序，
    保留其计算见证，以 Hom 相等刻画相互蕴含，不要求对谓词取商。 *)

(** Entailment retains a factor between the selected truth inverse images. *)

(** 蕴含保留选定真逆像之间的分解因子。 *)

Definition predicate_le {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}
    {X : @Ob C} (f g : Hom X Ω)
  : Type
  := ClassifiedSub f ≲Sub ClassifiedSub g.

Infix "⊢Ω" := predicate_le
  (at level 50, no associativity) : cat_scope.

(** ** Entailment and Substitution

    Fix named terminal, classifier and pullback choices in [C]. Products
    are unnecessary for entailment, reflection of equality, truth or
    substitution. The selected pullback domains and factors remain data. *)

(** ** 蕴含与代入

    在 [C] 中固定具名终对象、分类子和拉回选择。蕴含、相等反射、真及代入
    不需要积；选定拉回定义域与分解因子保持为数据。 *)

Section Entailment.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}.

(** Reuse the general inverse-image preorder construction with the
    transparent subobject preorder. Clients enable this value explicitly. *)

(** 以透明子对象预序复用一般的预序逆像构造，由使用者显式启用此值。 *)

Definition PredicatePreorder (X : @Ob C)
  : PreOrder (@predicate_le C HT HC PB X)
  := @pullback_preorder ((@Hom C) X Ω) (Sub X) (Sub_le X)
      (SubFactorPreorder X) (@ClassifiedSub C HT HC PB X).

(** Entailment identity keeps the identity factor. *)

(** 蕴含的恒等保留恒等因子。 *)

Definition predicate_le_refl {X : @Ob C} (f : Hom X Ω)
  : f ⊢Ω f
  := sub_factor_id (ClassifiedSub f).

(** Entailment composition composes the supplied factors. *)

(** 蕴含的复合将给定分解因子复合。 *)

Definition predicate_le_trans {X : @Ob C} {f g h : Hom X Ω}
    (Hfg : f ⊢Ω g) (Hgh : g ⊢Ω h)
  : f ⊢Ω h
  := sub_factor_comp Hfg Hgh.

(** Transparent comparison factors for equal predicates use classifier
    reflection, leaving the existing Proper registration unchanged. *)

(** 相等谓词的透明比较因子使用分类反射，不改变已有的 Proper 注册。 *)

Definition classified_sub_congr {X : @Ob C} {f g : Hom X Ω} (H : f ≈ g)
  : ClassifiedSub f ~Sub ClassifiedSub g.
Proof.
  apply (snd (classifier_char_subobject_eq _ _)).
  rewrite !classified_sub_char. exact H.
Defined.

(** Mutual entailment detects precisely the specified predicate equality. *)

(** 相互蕴含恰好检测指定的谓词相等。 *)

Definition predicate_le_eq {X : @Ob C} (f g : Hom X Ω)
  : (f ⊢Ω g ∧ g ⊢Ω f) ↔ f ≈ g.
Proof.
  split.
  - intros H.
    pose (K := classifier_char_subobject_proper _ _ H).
    rewrite !classified_sub_char in K. exact K.
  - intros H. exact (classified_sub_congr H).
Defined.

(** Replacing either predicate by an equal one transports its actual
    entailment factors, without equating proof records. *)

(** 将任一谓词换为相等谓词，运输其实际蕴含因子，不比较证明记录。 *)

Global Instance predicate_le_proper {X : @Ob C}
  : Proper (≈[X, Ω] ==> ≈[X, Ω] ==> iffT) predicate_le.
Proof.
  intros f f' Hf g g' Hg.
  pose (F := classified_sub_congr Hf).
  pose (G := classified_sub_congr Hg). split; intros K.
  - exact (sub_factor_comp (snd F) (sub_factor_comp K (fst G))).
  - exact (sub_factor_comp (fst F) (sub_factor_comp K (snd G))).
Defined.

(** Entailment says that the consequent is true on the antecedent's
    selected subobject. The reverse criterion retains its factor. *)

(** 蕴含表示后件在前件的选定子对象上为真；判据的反向保留分解因子。 *)

Definition predicate_le_truth {X : @Ob C} (f g : Hom X Ω)
  : f ⊢Ω g ↔ g ∘ ClassifiedSub f ≈ truth ∘ !.
Proof.
  pose (H := classifier_char_factor (sub_mono _ (ClassifiedSub g))
    (ClassifiedSub f)). split.
  - intros K. pose (T := snd H K).
    rewrite classified_sub_char in T. exact T.
  - intros K. apply (fst H). rewrite classified_sub_char. exact K.
Defined.

(** Classifying after substitution agrees with the existing inverse-image
    operation. Reflection supplies transparent comparison factors. *)

(** 代入后分类与既有逆像操作相容，反射给出透明比较因子。 *)

Definition classified_sub_precomp {X Y : @Ob C}
    (k : Hom X Y) (f : Hom Y Ω)
  : ClassifiedSub (f ∘ k) ~Sub Sub_fmap k (ClassifiedSub f).
Proof.
  apply (snd (classifier_char_subobject_eq _ _)).
  rewrite classified_sub_char. symmetry.
  transitivity (χ (sub_mono _ (ClassifiedSub f)) ∘ k).
  - exact (classifier_char_pullback k (sub_mono _ (ClassifiedSub f))
      (sub_mono _ (Sub_fmap k (ClassifiedSub f)))
      (pb2 k (ClassifiedSub f)) pullback_universal).
  - rewrite classified_sub_char. reflexivity.
Defined.

(** Substitution preserves entailment by inverse-image monotonicity,
    using the same selected pullbacks throughout. *)

(** 由逆像单调性，代入保持蕴含，全程使用同一组选定拉回。 *)

Definition predicate_le_subst {X Y : @Ob C} (k : Hom X Y)
    {f g : Hom Y Ω} (H : f ⊢Ω g)
  : f ∘ k ⊢Ω g ∘ k
  := sub_factor_comp (fst (classified_sub_precomp k f))
      (sub_factor_comp (sub_inverse_le k H)
        (snd (classified_sub_precomp k g))).

(** The constantly true predicate is greatest in entailment order. *)

(** 恒真谓词是蕴含序的最大元。 *)

Definition predicate_le_top {X : @Ob C} (f : Hom X Ω)
  : f ⊢Ω truth ∘ !.
Proof.
  apply (snd (predicate_le_truth f (truth ∘ !))).
  rewrite comp_assoc, (term_η (! ∘ ClassifiedSub f)). reflexivity.
Defined.

End Entailment.

(** ** Conjunction as Greatest Lower Bound

    Add a named product choice for classifier conjunction. Transfer the
    existing subobject-intersection universal property and its factors;
    this does not introduce a separate chosen lattice structure. *)

(** ** 合取为最大下界

    为分类对象的合取增加具名积选择。传递既有子对象交的泛性质及其因子，
    不另引入选定格结构。 *)

Section ConjunctionOrder.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C}.

(** A predicate entails a conjunction exactly when it entails both
    conjuncts, with Type-valued witness maps in both directions. *)

(** 谓词蕴含合取，当且仅当它蕴含两个合取项，两个方向均为 Type 值见证映射。 *)

Definition predicate_conjunction_universal {X : @Ob C} (r f g : Hom X Ω)
  : r ⊢Ω f ∧Ω g ↔ r ⊢Ω f ∧ r ⊢Ω g.
Proof.
  pose (E := classified_conjunction_sub f g).
  pose (U := sub_intersection_universal
    (ClassifiedSub f) (ClassifiedSub g) (ClassifiedSub r)). split.
  - intros H. exact (fst U (sub_factor_comp H (fst E))).
  - intros H. exact (sub_factor_comp (snd U H) (snd E)).
Defined.

(** Conjunction entails its first conjunct. *)

(** 合取蕴含第一项。 *)

Definition predicate_conjunction_left {X : @Ob C} (f g : Hom X Ω)
  : f ∧Ω g ⊢Ω f
  := fst (fst (predicate_conjunction_universal (f ∧Ω g) f g)
      (predicate_le_refl (f ∧Ω g))).

(** Conjunction entails its second conjunct. *)

(** 合取蕴含第二项。 *)

Definition predicate_conjunction_right {X : @Ob C} (f g : Hom X Ω)
  : f ∧Ω g ⊢Ω g
  := snd (fst (predicate_conjunction_universal (f ∧Ω g) f g)
      (predicate_le_refl (f ∧Ω g))).

(** Combine the two supplied entailment witnesses through the same
    greatest-lower-bound mediator. *)

(** 通过同一最大下界中介组合两个给定蕴含见证。 *)

Definition predicate_conjunction_pair {X : @Ob C} {r f g : Hom X Ω}
    (Hf : r ⊢Ω f) (Hg : r ⊢Ω g)
  : r ⊢Ω f ∧Ω g
  := snd (predicate_conjunction_universal r f g) (Hf, Hg).

(** Entailment is equivalently the meet equation, retaining the reverse
    factor computed by classifier reflection and conjunction elimination. *)

(** 蕴含等价于交方程，反向保留由分类反射及合取消去计算出的分解因子。 *)

Definition predicate_le_conjunction {X : @Ob C} (f g : Hom X Ω)
  : f ⊢Ω g ↔ f ∧Ω g ≈ f.
Proof.
  split.
  - intros H. apply (fst (predicate_le_eq _ _)). split.
    + apply predicate_conjunction_left.
    + exact (predicate_conjunction_pair (predicate_le_refl f) H).
  - intros H.
    exact (sub_factor_comp (snd (classified_sub_congr H))
      (predicate_conjunction_right f g)).
Defined.

End ConjunctionOrder.
