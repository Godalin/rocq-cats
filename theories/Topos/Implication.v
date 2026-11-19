From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Equalizer
  Cat.EqualizerMorphism
  Cat.Pullback
  Cat.Morphism
  Cat.SubobjectIntersection
  Instance.Set.Subobject
  Instance.Set.SubobjectRestriction
  Topos.Sub
  Topos.Representation
  Topos.Conjunction
  Topos.PredicateOrder.

(** * Implication on the Classifier

    Classify the equalizer of conjunction and first projection. Its truth
    criterion is the meet equation. Restriction of subobjects then gives
    the Heyting adjunction with actual entailment factors. *)

(** * 分类对象上的蕴含

    分类合取与第一投影的等化子，以交方程刻画其为真。随后由子对象限制得到
    保留实际蕴含因子的 Heyting 伴随律。 *)

(** Classify the selected equalizer inclusion of conjunction and first
    projection, using named choices without any selected pullbacks. *)

(** 分类合取与第一投影的选定等化子包含，使用具名选择，不要求选定拉回。 *)

Definition Imp {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasEqualizer C}
  : Hom (Ω × Ω) Ω
  := χ (EqualizerMono (equalizer_universal (f := Conj) (g := π1))).

(** Apply the implication arrow to predicates over one context. *)

(** 将蕴含箭头作用于同一上下文上的谓词。 *)

Definition implication {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasEqualizer C} {X : C} (f g : Hom X Ω)
  : Hom X Ω
  := Imp ∘ ⟨f, g⟩.

Infix "⇒Ω" := implication
  (at level 46, right associativity) : hom_scope.

(** ** Truth and Substitution for Implication

    Fix named terminal, classifier, product and equalizer choices. The
    construction and its laws do not need chosen pullbacks, exponentials
    or any additional topos properties. *)

(** ** 蕴含的真与代入

    固定具名终对象、分类子、积及等化子选择。构造及其定律不需要选定拉回、
    指数或额外拓扑斯性质。 *)

Section Implication.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasEqualizer C}.

(** Implication respects both predicates' specified equality. *)

(** 蕴含对两个谓词的指定相等均保相等。 *)

Global Instance implication_proper {X : C}
  : Proper (≈[X, Ω] ==> ≈[X, Ω] ==> ≈[X, Ω]) implication.
Proof.
  intros f f' Hf g g' Hg. unfold implication.
  apply comp_proper; [reflexivity | apply product_pair_proper; assumption].
Qed.

(** Implication commutes with substitution using the same equalizer. *)

(** 蕴含使用同一等化子与代入相容。 *)

Theorem implication_comp {X Y : C} (f g : Hom Y Ω) (k : Hom X Y)
  : (f ⇒Ω g) ∘ k ≈ (f ∘ k) ⇒Ω (g ∘ k).
Proof. unfold implication. rewrite comp_assoc, product_comp_r. reflexivity. Qed.

(** Implication is true exactly when conjunction equals its first
    argument. The factor criterion retains the equalizer's mediator. *)

(** 蕴含为真，当且仅当合取等于其第一项；分解判据保留等化子中介。 *)

Definition implication_true {X : C} (f g : Hom X Ω)
  : f ⇒Ω g ≈ truth ∘ ! ↔ f ∧Ω g ≈ f.
Proof.
  pose (E := equalizer_universal (f := Conj) (g := π1)).
  pose (F := classifier_char_factor (EqualizerMono E) ⟨f, g⟩).
  pose (U := equalizer_factor E ⟨f, g⟩). split.
  - intros H. pose (K := fst U (fst F H)).
    rewrite product_β1 in K. exact K.
  - intros H. apply (snd F). apply (snd U).
    rewrite product_β1. exact H.
Defined.

End Implication.

(** ** Restriction and the Heyting Adjunction

    Add named pullbacks for classified subobjects and entailment. Transfer
    the general inverse-image restriction correspondence; the implication
    arrow still uses exactly the supplied equalizer choice. *)

(** ** 限制与 Heyting 伴随

    为分类子对象及蕴含序增加具名拉回。传递一般逆像限制对应；蕴含箭头仍
    恰好使用给定的等化子选择。 *)

Section ImplicationOrder.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HE : !HasEqualizer C}.

(** Entailment under a conjunct is entailment after restricting both
    predicates to that conjunct's selected classified subobject. *)

(** 在一个合取项之下的蕴含，等价于将两个谓词限制到该项的选定分类子对象
    后的蕴含。 *)

Definition predicate_le_restriction {X : C} (r f g : Hom X Ω)
  : r ∧Ω f ⊢Ω g ↔ f ∘ ClassifiedSub r ⊢Ω g ∘ ClassifiedSub r.
Proof.
  pose (E := classified_conjunction_sub r f).
  pose (F := classified_sub_precomp (ClassifiedSub r) f).
  pose (G := classified_sub_precomp (ClassifiedSub r) g).
  pose (U := sub_inverse_restriction
    (ClassifiedSub r) (ClassifiedSub f) (ClassifiedSub g)). split.
  - intros H. exact (sub_factor_comp (fst F)
      (sub_factor_comp (fst U (sub_factor_comp (snd E) H)) (snd G))).
  - intros H. exact (sub_factor_comp (fst E)
      (snd U (sub_factor_comp (snd F) (sub_factor_comp H (fst G))))).
Defined.

(** Internal implication is true exactly when its antecedent entails its
    consequent. Both directions preserve Type-valued witnesses. *)

(** 内部蕴含为真，当且仅当前件蕴含后件；两个方向均保留 Type 值见证。 *)

Definition implication_entailment {X : C} (f g : Hom X Ω)
  : f ⇒Ω g ≈ truth ∘ ! ↔ f ⊢Ω g.
Proof.
  split.
  - intros H. exact (snd (predicate_le_conjunction f g)
      (fst (implication_true f g) H)).
  - intros H. exact (snd (implication_true f g)
      (fst (predicate_le_conjunction f g) H)).
Defined.

(** Implication is right adjoint to conjunction in each predicate order.
    These are maps of actual factors, not propositional truncations. *)

(** 在每个谓词序中，蕴含是合取的右伴随；此处是实际分解因子的映射，不作
    命题截断。 *)

Definition predicate_implication_universal {X : C} (r f g : Hom X Ω)
  : r ∧Ω f ⊢Ω g ↔ r ⊢Ω f ⇒Ω g.
Proof.
  pose (R := predicate_le_restriction r f g).
  pose (T := predicate_le_truth r (f ⇒Ω g)).
  pose (I := implication_entailment
    (f ∘ ClassifiedSub r) (g ∘ ClassifiedSub r)). split.
  - intros H. apply (snd T). rewrite implication_comp.
    exact (snd I (fst R H)).
  - intros H. apply (snd R). apply (fst I).
    pose (K := fst T H). rewrite implication_comp in K. exact K.
Defined.

(** Evaluation combines an implication with its antecedent. *)

(** 求值将内部蕴含与其前件组合。 *)

Definition predicate_implication_eval {X : C} (f g : Hom X Ω)
  : (f ⇒Ω g) ∧Ω f ⊢Ω g
  := snd (predicate_implication_universal (f ⇒Ω g) f g)
      (predicate_le_refl (f ⇒Ω g)).

End ImplicationOrder.
