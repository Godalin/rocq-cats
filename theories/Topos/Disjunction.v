From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Equalizer
  Cat.Pullback
  Cat.Morphism
  Cat.SubobjectIntersection
  Topos.Sub
  Topos.Representation
  Topos.Conjunction
  Topos.PredicateOrder
  Topos.Implication
  Topos.ImplicationLaws
  Topos.Forall
  Topos.Bottom.

(** * Disjunction from Implication and Universal Quantification

    Quantify the common upper bound of two predicates. Reuse the Heyting
    adjunction and projection quantifier to retain actual introduction
    and elimination factors, without assuming joins or colimits. *)

(** * 由蕴含与全称量化构造析取

    对两个谓词的共同上界作量化；复用 Heyting 伴随与投影量词，保留实际引入
    和消去因子，不预设并或余极限。 *)

(** In an extended context, a common upper bound implies the variable
    upper bound. All operations use the supplied product/equalizer data. *)

(** 在扩张上下文中，共同上界蕴含变量上界；所有操作使用给定积／等化子数据。 *)

Definition disjunction_body {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{HP : !HasProduct C}
    `{HE : !HasEqualizer C} {X : C} (f g : Hom X Ω)
  : Hom (X × Ω) Ω
  := (((f ∘ π1) ⇒Ω π2) ∧Ω ((g ∘ π1) ⇒Ω π2)) ⇒Ω π2.

(** Quantify the variable upper bound for the two classifier projections. *)

(** 对分类对象的两个投影，量化其变量上界。 *)

Definition Disj {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{HP : !HasProduct C}
    `{HX : !HasExponential HP} `{HE : !HasEqualizer C}
  : Hom (Ω × Ω) Ω
  := ∀Ω[Ω] (disjunction_body (π1 : Hom (Ω × Ω) Ω) π2).

(** Apply the single disjunction arrow to a pair of predicates. *)

(** 将同一析取箭头作用于一对谓词。 *)

Definition disjunction {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{HP : !HasProduct C}
    `{HX : !HasExponential HP} `{HE : !HasEqualizer C}
    {X : C} (f g : Hom X Ω)
  : Hom X Ω
  := Disj ∘ ⟨f, g⟩.

Infix "∨Ω" := disjunction
  (at level 46, right associativity) : hom_scope.

(** ** Construction and Substitution

    Fix named terminal, classifier, products, relative exponentials and
    equalizers. The Church formula and its substitution laws do not need
    selected pullbacks. *)

(** ** 构造与代入

    固定具名终对象、分类子、积、相对指数及等化子。Church 公式及其代入律
    不要求选定拉回。 *)

Section Disjunction.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{HP : !HasProduct C}
    `{HX : !HasExponential HP} `{HE : !HasEqualizer C}.

(** The body respects both predicates before quantification. *)

(** 公式体在量化之前即对两个谓词保相等。 *)

Global Instance disjunction_body_proper {X : C}
  : Proper (≈[X, Ω] ==> ≈[X, Ω] ==> ≈[X × Ω, Ω])
      disjunction_body.
Proof.
  intros f f' Hf g g' Hg. unfold disjunction_body.
  rewrite Hf, Hg. reflexivity.
Qed.

(** Disjunction respects the specified equality of both predicates. *)

(** 析取对两个谓词的指定相等均保相等。 *)

Global Instance disjunction_proper {X : C}
  : Proper (≈[X, Ω] ==> ≈[X, Ω] ==> ≈[X, Ω]) disjunction.
Proof.
  intros f f' Hf g g' Hg. unfold disjunction.
  apply comp_proper; [reflexivity | apply product_pair_proper; assumption].
Qed.

(** Substitution acts on the body while retaining its truth-value variable. *)

(** 代入作用于公式体，同时保留其真值变量。 *)

Theorem disjunction_body_comp {X Y : C} (f g : Hom Y Ω) (k : Hom X Y)
  : disjunction_body f g ∘ (k × id)
    ≈ disjunction_body (f ∘ k) (g ∘ k).
Proof.
  unfold disjunction_body.
  rewrite implication_comp, conjunction_comp, !implication_comp.
  rewrite !comp_assoc, cross_η, product_β1, product_β2, comp_id_l.
  reflexivity.
Qed.

(** The global arrow has the same Church formula in every context. *)

(** 全局箭头在每个上下文中具有同一 Church 公式。 *)

Theorem disjunction_as_forall {X : C} (f g : Hom X Ω)
  : f ∨Ω g ≈ ∀Ω[Ω] (disjunction_body f g).
Proof.
  unfold disjunction, Disj. rewrite forall_predicate_comp.
  rewrite disjunction_body_comp, product_β1, product_β2. reflexivity.
Qed.

(** Disjunction commutes with substitution using the same chosen data. *)

(** 析取使用同一组选定数据与代入相容。 *)

Theorem disjunction_comp {X Y : C} (f g : Hom Y Ω) (k : Hom X Y)
  : (f ∨Ω g) ∘ k ≈ (f ∘ k) ∨Ω (g ∘ k).
Proof. unfold disjunction. rewrite comp_assoc, product_comp_r. reflexivity. Qed.

(** Instantiate the body by a proposed common upper bound. *)

(** 用候选共同上界实例化公式体。 *)

Theorem disjunction_body_instantiate {X : C} (f g r : Hom X Ω)
  : disjunction_body f g ∘ ⟨id, r⟩
    ≈ ((f ⇒Ω r) ∧Ω (g ⇒Ω r)) ⇒Ω r.
Proof.
  unfold disjunction_body.
  rewrite implication_comp, conjunction_comp, !implication_comp.
  rewrite !comp_assoc, product_β1, product_β2, !comp_id_r. reflexivity.
Qed.

End Disjunction.

(** ** Least Upper Bounds with Computational Factors

    Add named pullbacks for the entailment order. Exchange proves both
    introductions, and quantifier instantiation proves leastness. No
    lattice bundle, classical logic or global model choices are used. *)

(** ** 保留计算因子的最小上界

    为蕴含序增加具名拉回。交换给出两个引入，全称实例化给出最小性；不使用
    格束、经典逻辑或全局模型选择。 *)

Section DisjunctionOrder.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HX : !HasExponential HP}
    `{HE : !HasEqualizer C}.

(** The left predicate entails the Church formula by implication exchange. *)

(** 左谓词通过蕴含交换蕴含 Church 公式。 *)

Definition predicate_disjunction_left {X : C} (f g : Hom X Ω)
  : f ⊢Ω f ∨Ω g.
Proof.
  pose (u := f ∘ (π1 : Hom (X × Ω) X)).
  pose (v := g ∘ (π1 : Hom (X × Ω) X)).
  pose (p := (π2 : Hom (X × Ω) Ω)).
  pose (K := (u ⇒Ω p) ∧Ω (v ⇒Ω p)).
  pose (H := fst (predicate_implication_exchange K u p)
    (predicate_conjunction_left (u ⇒Ω p) (v ⇒Ω p))).
  exact (sub_factor_comp
    (fst (predicate_forall_universal Ω f (disjunction_body f g)) H)
    (snd (classified_sub_congr (disjunction_as_forall f g)))).
Defined.

(** The right predicate entails the same formula using the other projection. *)

(** 右谓词使用另一投影蕴含同一公式。 *)

Definition predicate_disjunction_right {X : C} (f g : Hom X Ω)
  : g ⊢Ω f ∨Ω g.
Proof.
  pose (u := f ∘ (π1 : Hom (X × Ω) X)).
  pose (v := g ∘ (π1 : Hom (X × Ω) X)).
  pose (p := (π2 : Hom (X × Ω) Ω)).
  pose (K := (u ⇒Ω p) ∧Ω (v ⇒Ω p)).
  pose (H := fst (predicate_implication_exchange K v p)
    (predicate_conjunction_right (u ⇒Ω p) (v ⇒Ω p))).
  exact (sub_factor_comp
    (fst (predicate_forall_universal Ω g (disjunction_body f g)) H)
    (snd (classified_sub_congr (disjunction_as_forall f g)))).
Defined.

(** Disjunction is the least upper bound. Both directions preserve
    Type-valued factors, without truncating the two input entailments. *)

(** 析取是最小上界；两个方向保留 Type 值因子，不截断两个输入蕴含。 *)

Definition predicate_disjunction_universal {X : C} (f g r : Hom X Ω)
  : f ∨Ω g ⊢Ω r ↔ (f ⊢Ω r ∧ g ⊢Ω r).
Proof.
  split.
  - intros H. split.
    + exact (sub_factor_comp (predicate_disjunction_left f g) H).
    + exact (sub_factor_comp (predicate_disjunction_right f g) H).
  - intros H.
    assert (T : (f ⇒Ω r) ∧Ω (g ⇒Ω r) ≈ truth ∘ !).
    { apply (snd (conjunction_true _ _)). split.
      - exact (snd (implication_entailment f r) (fst H)).
      - exact (snd (implication_entailment g r) (snd H)). }
    assert (E : ((f ⇒Ω r) ∧Ω (g ⇒Ω r)) ⇒Ω r ≈ r).
    { rewrite T. apply implication_truth. }
    exact (sub_factor_comp
      (fst (classified_sub_congr (disjunction_as_forall f g)))
      (sub_factor_comp
        (predicate_forall_instantiate Ω (disjunction_body f g) r)
        (sub_factor_comp
          (fst (classified_sub_congr (disjunction_body_instantiate f g r)))
          (fst (classified_sub_congr E))))).
Defined.

(** Monotonicity follows from the least-upper-bound factors. *)

(** 单调性来自最小上界因子。 *)

Definition predicate_disjunction_mono {X : C} {f f' g g' : Hom X Ω}
    (Hf : f ⊢Ω f') (Hg : g ⊢Ω g')
  : f ∨Ω g ⊢Ω f' ∨Ω g'
  := snd (predicate_disjunction_universal f g (f' ∨Ω g'))
      (sub_factor_comp Hf (predicate_disjunction_left f' g'),
       sub_factor_comp Hg (predicate_disjunction_right f' g')).

(** Least upper bounds commute up to the specified predicate equality. *)

(** 最小上界在指定谓词相等下满足交换律。 *)

Theorem disjunction_comm {X : C} (f g : Hom X Ω)
  : f ∨Ω g ≈ g ∨Ω f.
Proof.
  apply (fst (predicate_le_eq _ _)). split;
    apply (snd (predicate_disjunction_universal _ _ _)); split;
    first [apply predicate_disjunction_left | apply predicate_disjunction_right].
Qed.

(** Repeating a predicate leaves the least upper bound unchanged. *)

(** 重复同一谓词不改变最小上界。 *)

Theorem disjunction_idem {X : C} (f : Hom X Ω)
  : f ∨Ω f ≈ f.
Proof.
  apply (fst (predicate_le_eq _ _)). split.
  - apply (snd (predicate_disjunction_universal _ _ _)). split;
      apply predicate_le_refl.
  - apply predicate_disjunction_left.
Qed.

(** Nested least upper bounds associate without identifying factor records. *)

(** 嵌套最小上界满足结合律，不要求因子记录相等。 *)

Theorem disjunction_assoc {X : C} (f g h : Hom X Ω)
  : (f ∨Ω g) ∨Ω h ≈ f ∨Ω (g ∨Ω h).
Proof.
  apply (fst (predicate_le_eq _ _)). split.
  - apply (snd (predicate_disjunction_universal _ _ _)). split.
    + apply (snd (predicate_disjunction_universal _ _ _)). split.
      * apply predicate_disjunction_left.
      * exact (sub_factor_comp (predicate_disjunction_left g h)
          (predicate_disjunction_right f (g ∨Ω h))).
    + exact (sub_factor_comp (predicate_disjunction_right g h)
        (predicate_disjunction_right f (g ∨Ω h))).
  - apply (snd (predicate_disjunction_universal _ _ _)). split.
    + exact (sub_factor_comp (predicate_disjunction_left f g)
        (predicate_disjunction_left (f ∨Ω g) h)).
    + apply (snd (predicate_disjunction_universal _ _ _)). split.
      * exact (sub_factor_comp (predicate_disjunction_right f g)
          (predicate_disjunction_left (f ∨Ω g) h)).
      * apply predicate_disjunction_right.
Qed.

(** False is a unit for disjunction by its previously proved leastness. *)

(** 由假已经证明的最小性，得到它是析取的单位元。 *)

Theorem disjunction_bottom {X : C} (f : Hom X Ω)
  : f ∨Ω ⊥Ω ≈ f.
Proof.
  apply (fst (predicate_le_eq _ _)). split.
  - apply (snd (predicate_disjunction_universal _ _ _)). split.
    + apply predicate_le_refl.
    + apply predicate_bottom.
  - apply predicate_disjunction_left.
Qed.

End DisjunctionOrder.
