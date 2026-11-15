From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Pullback
  Cat.Morphism
  Cat.SubobjectIntersection
  Instance.Set.Subobject
  Topos.Sub
  Topos.Representation
  Topos.PredicateOrder
  Topos.Forall.

(** * Bottom Predicates and Least Subobjects

    Quantify over the truth-value object to obtain false. Instantiation
    gives its leastness in each predicate order, and classification
    transfers the same computational factors to subobjects. *)

(** * 底谓词与最小子对象

    对真值对象作全称量化以得到假。实例化给出它在每个谓词序中的最小性，
    分类将同一组计算因子传到子对象。 *)

(** False is the universal quantification of the truth-value variable. *)

(** 假是对真值变量作全称量化得到的结果。 *)

Definition Bottom {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasExponential HP}
  : Hom 1 Ω
  := ∀Ω[Ω] (π2 : Hom (1 × Ω) Ω).

(** Substitute the same global false arrow into any context. *)

(** 将同一全局假箭头代入任意上下文。 *)

Definition bottom {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X : C}
  : Hom X Ω
  := Bottom ∘ !.

Notation "'⊥Ω'" := bottom : hom_scope.

(** ** False in a Context

    Fix named terminal, classifier, product and exponential choices.
    Universal quantification commutes with context substitution, so the
    global definition also quantifies the variable in any context. *)

(** ** 上下文中的假

    固定具名终对象、分类子、积及指数选择。全称量化与上下文代入相容，因此
    全局定义在任意上下文中仍是对真值变量的量化。 *)

Section Bottom.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{HP : !HasProduct C}
    `{HE : !HasExponential HP}.

(** Substitution preserves the constantly false predicate. *)

(** 代入保持恒假谓词。 *)

Theorem bottom_comp {X Y : C} (f : Hom X Y)
  : (⊥Ω : Hom Y Ω) ∘ f ≈ ⊥Ω.
Proof.
  unfold bottom. rewrite comp_assoc, (term_η (! ∘ f)). reflexivity.
Qed.

(** False is quantification of the variable in the supplied context,
    without identifying that context with a terminal product. *)

(** 假是在给定上下文中对变量的量化，不将该上下文与终对象的积识别。 *)

Theorem bottom_forall (X : C)
  : (⊥Ω : Hom X Ω) ≈ ∀Ω[Ω] (π2 : Hom (X × Ω) Ω).
Proof.
  unfold bottom, Bottom. rewrite forall_predicate_comp.
  apply forall_predicate_proper.
  rewrite cross_η, product_β2, comp_id_l. reflexivity.
Qed.

End Bottom.

(** ** Least Predicates and Subobjects

    Add named pullbacks for the Type-valued entailment order. Instantiate
    the quantified truth-value variable by the target predicate; retain
    the resulting factors and transfer them through classification. *)

(** ** 最小谓词与子对象

    为 Type 值蕴含序增加具名拉回。用目标谓词实例化全称量化的真值变量，
    保留得到的因子，再通过分类将其传到子对象。 *)

Section BottomOrder.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** False entails any predicate by universal instantiation. *)

(** 通过全称实例化，假蕴含任意谓词。 *)

Definition predicate_bottom {X : C} (f : Hom X Ω)
  : ⊥Ω ⊢Ω f.
Proof.
  pose (H := predicate_forall_instantiate Ω
    (π2 : Hom (X × Ω) Ω) f).
  assert (K : (π2 : Hom (X × Ω) Ω) ∘ ⟨id, f⟩ ≈ f).
  { apply product_β2. }
  exact (sub_factor_comp (fst (classified_sub_congr (bottom_forall X)))
    (sub_factor_comp H (fst (classified_sub_congr K)))).
Defined.

(** Entailing false detects equality with false; the reverse direction
    retains the equality-reflection factor. *)

(** 蕴含假刻画与假的相等；反向保留相等反射给出的因子。 *)

Definition predicate_bottom_eq {X : C} (f : Hom X Ω)
  : f ⊢Ω ⊥Ω ↔ f ≈ ⊥Ω.
Proof.
  split.
  - intros H. exact (fst (predicate_le_eq f ⊥Ω) (H, predicate_bottom f)).
  - intros H. exact (fst (classified_sub_congr H)).
Defined.

(** Every least predicate is equal to the chosen false predicate in the
    specified hom equality. *)

(** 每个最小谓词都按指定 Hom 相等与选定的假谓词相等。 *)

Theorem predicate_bottom_unique {X : C} (f : Hom X Ω)
    (H : ∀ g : Hom X Ω, f ⊢Ω g)
  : f ≈ ⊥Ω.
Proof. exact (fst (predicate_bottom_eq f) (H ⊥Ω)). Qed.

(** Classify the false predicate using the same selected truth inverse
    image as every other predicate. *)

(** 与其他谓词使用同一选定真逆像，对假谓词进行分类。 *)

Definition SubBottom (X : C)
  : Sub X
  := ClassifiedSub (⊥Ω : Hom X Ω).

(** The classified false predicate factors through every subobject. *)

(** 假谓词的分类子对象经过每个子对象分解。 *)

Definition sub_bottom {X : C} (s : Sub X)
  : SubBottom X ≲Sub s
  := sub_factor_comp (predicate_bottom (χ (sub_mono _ s)))
      (fst (classified_char_sub s)).

(** Least subobjects are equivalent by their actual mutual factors. *)

(** 最小子对象通过实际的相互分解因子等价。 *)

Definition sub_bottom_unique {X : C} (s : Sub X)
    (H : ∀ t : Sub X, s ≲Sub t)
  : s ~Sub SubBottom X
  := (H (SubBottom X), sub_bottom s).

(** Inverse image preserves the least subobject by the existing
    substitution comparison and stability of false. *)

(** 由已有代入比较及假的稳定性，逆像保持最小子对象。 *)

Definition sub_inverse_bottom {X Y : C} (f : Hom X Y)
  : Sub_fmap f (SubBottom Y) ~Sub SubBottom X.
Proof.
  pose (E := classified_sub_precomp f (⊥Ω : Hom Y Ω)).
  pose (F := classified_sub_congr (bottom_comp f)). split.
  - exact (sub_factor_comp (snd E) (fst F)).
  - exact (sub_factor_comp (snd F) (fst E)).
Defined.

(** Explicitly package the least subobject as initial in the thin
    subobject category, through the original opposite-terminal interface.
    Import does not enable this choice automatically. *)

(** 通过原有反范畴终对象接口，显式将最小子对象打包为子对象薄范畴中的始对象。
    导入不自动启用该选择。 *)

Program Definition SubCat_HasInitial (X : C)
  : HasInitial (SubCat X)
  :=
  {|hasOpTerminal :=
      {|Term := SubBottom X
      |}
  |}.
Next Obligation.
  intros s. exists (sub_bottom s).
  refine {|this := I
         ; that := _
         |}.
  intros. exact tt.
Defined.

End BottomOrder.
