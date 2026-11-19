From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Pullback
  Cat.Morphism
  Cat.SubobjectIntersection
  Topos.Sub
  Topos.Representation.

(** * Conjunction on the Classifier

    Classify paired truth to obtain conjunction. Its subobject
    interpretation reuses binary intersections, rather than introducing
    a second lattice interface or an additional chosen model structure. *)

(** * 分类对象上的合取

    分类成对真箭头以得到合取。其子对象解释复用二元交，不引入第二套格接口
    或额外的选定模型结构。 *)

(** ** Truth and Factorization

    Fix only a named terminal choice and subobject classifier in [C].
    The classifying square retains factors of generalized arrows through
    a monomorphism. No chosen pullbacks or products are required here. *)

(** ** 真与分解

    在 [C] 中仅固定具名终对象选择和子对象分类子。分类方形保留广义箭头
    经过单态射的分解因子，此处不要求选定拉回或积。 *)

Section Factorization.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HSC : !HasSubObjClassifier C HT}.

(** A characteristic arrow is true on a generalized element exactly when
    that element factors through the displayed monomorphism. *)

(** 特征箭头在一个广义元素上为真，当且仅当该元素经过所展示单态射分解。 *)

Definition classifier_char_factor {X Y Q : @Ob C}
    (m : X ↣ Y) (f : Hom Q Y)
  : χ m ∘ f ≈ truth ∘ ! ↔ is_factored_through m f.
Proof.
  pose (HP := this (classifier_char_unique (m := m))). split.
  - intros Hf.
    pose (u := snd HP Q f ! Hf).
    exists u.1. symmetry. exact (fst (this u.2)).
  - intros [h Hh]. rewrite Hh, <- comp_assoc, (fst HP), comp_assoc.
    rewrite (term_η (! ∘ h)). reflexivity.
Defined.

(** Identify a classifying arrow by its Type-valued factorization
    criterion on all generalized elements. Monicity supplies uniqueness
    of the retained mediators. *)

(** 由所有广义元素上的 Type 值分解判据确定分类箭头。单态性给出所保留中介
    的唯一性。 *)

Theorem classifier_char_by_factors {X Y : @Ob C} (m : X ↣ Y)
    (c : Hom Y Ω)
    (H : ∀ Q (f : Hom Q Y),
      c ∘ f ≈ truth ∘ ! ↔ is_factored_through m f)
  : c ≈ χ m.
Proof.
  apply (classifier_char_unique (m := m)). split.
  - apply (snd (H X m)). exists id. symmetry. apply comp_id_r.
  - intros Q q1 q2 Hq.
    assert (Hq' : c ∘ q1 ≈ truth ∘ !).
    { rewrite <- (term_η q2). exact Hq. }
    destruct (fst (H Q q1) Hq') as [h Hh].
    exists h. split.
    + split; [symmetry; exact Hh |].
      rewrite (term_η (! ∘ h)), (term_η q2). reflexivity.
    + intros k [Hk _]. apply m. rewrite Hk. exact Hh.
Qed.

End Factorization.

(** Classify the monomorphism from the terminal object whose two
    components are truth. This construction needs no chosen pullbacks. *)

(** 分类从终对象出发、两个分量均为真的单态射；此构造不需要选定拉回。 *)

Definition Conj {C : Cat} `{HT : !HasTerminal C}
    `{HSC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
  : Hom (Ω × Ω) Ω
  := χ (Mono_term ⟨truth, truth⟩).

(** Apply classifier conjunction to a pair of predicates over one context. *)

(** 将分类对象的合取作用于同一上下文上的一对谓词。 *)

Definition conjunction {C : Cat} `{HT : !HasTerminal C}
    `{HSC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    {X : @Ob C} (f g : Hom X Ω)
  : Hom X Ω
  := Conj ∘ ⟨f, g⟩.

Infix "∧Ω" := conjunction
  (at level 45, right associativity) : hom_scope.

(** ** Truth and Substitution for Conjunction

    Add chosen binary products to the named terminal and classifier.
    Conjunction is respectful and commutes with substitution by the
    existing pairing laws. Its truth criterion retains both equations. *)

(** ** 合取的真与代入

    在具名终对象和分类子之外增加选定二元积。合取保相等，并由已有配对定律
    与代入相容；其为真的判据保留两个方程。 *)

Section Conjunction.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HSC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}.

(** Equivalent predicates give equivalent conjunctions. *)

(** 等价谓词给出等价的合取。 *)

Global Instance conjunction_proper {X : @Ob C}
  : Proper (≈[X, Ω] ==> ≈[X, Ω] ==> ≈[X, Ω]) conjunction.
Proof.
  intros f f' Hf g g' Hg. unfold conjunction.
  apply comp_proper; [reflexivity | apply product_pair_proper; assumption].
Qed.

(** Substituting into conjunction substitutes into both predicates. *)

(** 对合取作代入，等于对两个谓词分别作代入。 *)

Theorem conjunction_comp {X Y : @Ob C} (f g : Hom Y Ω) (k : Hom X Y)
  : (f ∧Ω g) ∘ k ≈ (f ∘ k) ∧Ω (g ∘ k).
Proof. unfold conjunction. rewrite comp_assoc, product_comp_r. reflexivity. Qed.

(** A conjunction is true exactly when both predicates are true. *)

(** 合取为真，当且仅当两个谓词均为真。 *)

Definition conjunction_true {X : @Ob C} (f g : Hom X Ω)
  : f ∧Ω g ≈ truth ∘ ! ↔ f ≈ truth ∘ ! ∧ g ≈ truth ∘ !.
Proof.
  pose (H := classifier_char_factor (Mono_term ⟨truth, truth⟩) ⟨f, g⟩).
  split.
  - intros Hfg. destruct (fst H Hfg) as [h Hh].
    change (⟨f, g⟩ ≈ ⟨truth, truth⟩ ∘ h) in Hh. split.
    + transitivity (π1 ∘ ⟨f, g⟩); [symmetry; apply product_β1 |].
      rewrite Hh, <- comp_assoc, product_β1, (term_η h). reflexivity.
    + transitivity (π2 ∘ ⟨f, g⟩); [symmetry; apply product_β2 |].
      rewrite Hh, <- comp_assoc, product_β2, (term_η h). reflexivity.
  - intros [Hf Hg]. apply (snd H). exists !.
    simpl. rewrite product_comp_r. apply product_pair_proper; assumption.
Defined.

End Conjunction.

(** ** Interpreting Conjunction as Intersection

    Add a named pullback choice to reconstruct arbitrary predicates as
    subobjects. Classification then transports the already established
    intersection laws; no further logical principles are assumed. *)

(** ** 将合取解释为交

    增加具名拉回选择以将任意谓词重构为子对象。分类将已有的交定律传到合取，
    不假定其他逻辑原理。 *)

Section Intersection.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HSC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HPb : !HasPullback C}.

(** The intersection is classified by the conjunction of its two
    characteristic arrows. The proof reuses the arbitrary-arrow
    factorization property of subobject intersection. *)

(** 交由两个特征箭头的合取分类；证明复用子对象交对任意箭头的分解性质。 *)

Theorem classifier_char_intersection {X : @Ob C} (s t : Sub X)
  : χ (sub_mono _ (s ∩Sub t)) ≈
      χ (sub_mono _ s) ∧Ω χ (sub_mono _ t).
Proof.
  symmetry. apply classifier_char_by_factors.
  intros Q f. split.
  - intros Hf. rewrite conjunction_comp in Hf.
    destruct (fst (conjunction_true _ _) Hf) as [Hs Ht].
    apply (snd (sub_intersection_factor s t f)). split.
    + exact (fst (classifier_char_factor (sub_mono _ s) f) Hs).
    + exact (fst (classifier_char_factor (sub_mono _ t) f) Ht).
  - intros Hf. rewrite conjunction_comp.
    destruct (fst (sub_intersection_factor s t f) Hf) as [Hs Ht].
    apply (snd (conjunction_true _ _)). split.
    + exact (snd (classifier_char_factor (sub_mono _ s) f) Hs).
    + exact (snd (classifier_char_factor (sub_mono _ t) f) Ht).
Qed.

(** Reconstructing a conjunction gives the intersection of the two
    reconstructed subobjects, with transparent comparison factors. *)

(** 重构合取得到两个重构子对象的交，比较因子保持透明。 *)

Definition classified_conjunction_sub {X : @Ob C} (f g : Hom X Ω)
  : ClassifiedSub (f ∧Ω g) ~Sub ClassifiedSub f ∩Sub ClassifiedSub g.
Proof.
  apply (snd (classifier_char_subobject_eq _ _)).
  rewrite classifier_char_intersection, !classified_sub_char. reflexivity.
Defined.

(** Commutativity is transported from subobject intersection. *)

(** 交换律由子对象交传递。 *)

Theorem conjunction_comm {X : @Ob C} (f g : Hom X Ω)
  : f ∧Ω g ≈ g ∧Ω f.
Proof.
  pose (H := classifier_char_subobject_proper _ _
    (sub_intersection_comm (ClassifiedSub f) (ClassifiedSub g))).
  rewrite !classifier_char_intersection, !classified_sub_char in H. exact H.
Qed.

(** Associativity reuses the product-derived intersection associator. *)

(** 结合律复用由积得到的子对象交结合同构。 *)

Theorem conjunction_assoc {X : @Ob C} (f g h : Hom X Ω)
  : (f ∧Ω g) ∧Ω h ≈ f ∧Ω (g ∧Ω h).
Proof.
  pose (H := classifier_char_subobject_proper _ _
    (sub_intersection_assoc (ClassifiedSub f) (ClassifiedSub g)
      (ClassifiedSub h))).
  rewrite !classifier_char_intersection, !classified_sub_char in H. exact H.
Qed.

(** Repeating a predicate leaves its conjunction unchanged. *)

(** 同一谓词重复合取保持不变。 *)

Theorem conjunction_idem {X : @Ob C} (f : Hom X Ω)
  : f ∧Ω f ≈ f.
Proof.
  pose (H := classifier_char_subobject_proper _ _
    (sub_intersection_idem (ClassifiedSub f))).
  rewrite classifier_char_intersection, !classified_sub_char in H. exact H.
Qed.

(** The constantly true predicate is a unit for conjunction. *)

(** 恒真谓词是合取的单位元。 *)

Theorem conjunction_top {X : @Ob C} (f : Hom X Ω)
  : f ∧Ω (truth ∘ !) ≈ f.
Proof.
  pose (H := classifier_char_subobject_proper _ _
    (sub_intersection_top (ClassifiedSub f))).
  rewrite classifier_char_intersection, !classified_sub_char,
    classifier_char_top in H. exact H.
Qed.

End Intersection.
