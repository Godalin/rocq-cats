From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Equalizer
  Cat.EqualizerMorphism
  Cat.Pullback
  Cat.Morphism
  Cat.Limit.Finite
  Topos.Sub
  Topos.Representation
  Topos.Conjunction
  Topos.PredicateOrder
  Topos.Bottom.

(** * An Initial Object from Elementary Topos Choices

    Classify false on the selected terminal object. Its least-subobject
    property supplies actual arrows to every ambient object. Equalizers
    from the existing finite-limit conversion prove uniqueness; no choice,
    well-pointedness, NNO or independently selected initial object is used. *)

(** * 从初等拓扑斯选择得到始对象

    在选定终对象上分类假谓词，其最小子对象性质给出到每个环境对象的实际箭头。
    既有有限极限转换提供等化子以证明唯一性；不使用选择、良点性、NNO 或独立
    选定的始对象。 *)

Section ToposInitial.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** False remains true after substitution when it was true in the
    supplied context. This uses the original substitution law for false. *)

(** 若假在给定上下文中为真，则代入后仍为真；复用原有假谓词代入律。 *)

Theorem bottom_true_comp {X Y : C}
    (H : (⊥Ω : Hom Y Ω) ≈ truth ∘ !) (f : Hom X Y)
  : (⊥Ω : Hom X Ω) ≈ truth ∘ !.
Proof.
  rewrite <- (bottom_comp f), H, comp_assoc, term_comp_l. reflexivity.
Qed.

(** Every monomorphism into a context where false is true has a retained
    section. Factor its least subobject, then factor the identity through
    the classified false subobject using the existing truth criterion. *)

(** 指向假为真的上下文的每个单态射都有保留的截面。先分解最小子对象，再用
    既有为真判据，将恒等箭头经假谓词的分类子对象分解。 *)

Definition bottom_true_section {X Y : C}
    (H : (⊥Ω : Hom Y Ω) ≈ truth ∘ !) (m : X ↣ Y)
  : ∃ s : Hom Y X, m ∘ s ≈ (@Cats.Cat.Core.id C Y).
Proof.
  pose (B := SubBottom Y).
  assert (K : χ (sub_mono _ B) ∘ (@Cats.Cat.Core.id C Y) ≈ truth ∘ !).
  { unfold B, SubBottom. rewrite comp_id_r, classified_sub_char. exact H. }
  destruct (fst (classifier_char_factor (sub_mono _ B)
    (@Cats.Cat.Core.id C Y)) K)
    as [s Hs].
  pose (t := sub_bottom
    {|sub := X
    ; sub_mono := m
    |}).
  exists (t.1 ∘ s).
  rewrite <- comp_assoc, <- t.2. symmetry. exact Hs.
Defined.

(** A false context has at most one arrow to any object. Use the existing
    product/pullback equalizer, split its inclusion, and apply its original
    commutativity equation. No separate equalizer choice is required. *)

(** 假上下文到任意对象至多有一个箭头。使用既有积／拉回等化子，分裂其包含
    箭头，再应用原交换方程，不要求独立的等化子选择。 *)

Theorem bottom_true_hom_eq {X Y : C}
    (H : (⊥Ω : Hom X Ω) ≈ truth ∘ !) (f g : Hom X Y)
  : f ≈ g.
Proof.
  pose (EQ := @ProductPullbackEqualizer C HP PB).
  pose (e := @eqι C EQ X Y f g).
  assert (He : is_equalizer f g _ e).
  { exact (@equalizer_universal C EQ X Y f g). }
  destruct (bottom_true_section H (EqualizerMono He)) as [s Hs].
  transitivity (f ∘ (e ∘ s)).
  - rewrite Hs, comp_id_r. reflexivity.
  - rewrite <- comp_assoc, (fst He), comp_assoc, Hs, comp_id_r.
    reflexivity.
Qed.

(** The domain of false classified on the same selected terminal object
    is the candidate ambient initial object. *)

(** 在同一选定终对象上分类假的定义域，是环境始对象的候选。 *)

Definition ToposInitial
  : C
  := sub (SubBottom (1 : C)).

(** False is true on its own classified subobject, by the existing
    classified truth criterion. *)

(** 由既有分类为真判据，假在自身的分类子对象上为真。 *)

Theorem topos_initial_bottom
  : (⊥Ω : Hom ToposInitial Ω) ≈ truth ∘ !.
Proof.
  unfold ToposInitial.
  transitivity ((⊥Ω : Hom 1 Ω) ∘ (SubBottom (1 : C))).
  - symmetry. apply bottom_comp.
  - exact (fst (predicate_le_truth (⊥Ω : Hom 1 Ω) ⊥Ω)
    (predicate_le_refl ⊥Ω)).
Qed.

(** The product of the candidate initial object with any object is
    subterminal. A map into this product already makes its source false;
    the preceding equality theorem then compares all parallel arrows. *)

(** 候选始对象与任意对象的积是次终对象。映入此积的箭头使其源成为假上下文，
    因而前述相等定理可比较所有平行箭头。 *)

Program Definition InitialProductSub (X : C)
  : Sub (1 : C)
  :=
  {|sub := ToposInitial × X
  ; sub_mono :=
    {|mor := !
    |}
  |}.
Next Obligation.
  intros Q u v _.
  apply (bottom_true_hom_eq
    (bottom_true_comp topos_initial_bottom (π1 ∘ u))).
Qed.

(** Leastness factors false through that product subobject. Projection
    supplies the actual arrow to the arbitrary ambient object. *)

(** 最小性将假经此积子对象分解，随后投影给出到任意环境对象的实际箭头。 *)

Definition topos_init (X : C)
  : Hom ToposInitial X
  := π2 ∘ (sub_bottom (InitialProductSub X)).1.

(** This public native equation exposes the retained least-subobject
    factor rather than adding a new mediator choice. *)

(** 此公开原生方程暴露保留的最小子对象因子，不增加新的中介选择。 *)

Definition topos_init_data (X : C)
  : topos_init X = π2 ∘ (sub_bottom (InitialProductSub X)).1
  := eq_refl.

(** Every arrow from the candidate is equal to this actual chosen arrow. *)

(** 从候选对象出发的每个箭头都等于这个实际选定箭头。 *)

Theorem topos_init_unique {X : C} (f : Hom ToposInitial X)
  : f ≈ topos_init X.
Proof. apply (bottom_true_hom_eq topos_initial_bottom). Qed.

(** The ambient universal property retains the arrow and its uniqueness
    in Type, using the original opposite-terminal initial interface. *)

(** 环境泛性质在 Type 中保留箭头及唯一性，使用原有反终始对象接口。 *)

Definition topos_initial_universal
  : @is_initial C ToposInitial.
Proof.
  intros X. exists (topos_init X). split; [exact I |].
  intros f _. exact (topos_init_unique f).
Defined.

(** Explicitly enable the derived initial object. Importing this module
    registers no global structure and changes no Topos or ETCS fields. *)

(** 显式启用推导出的始对象；导入本模块不注册全局结构，不改变 Topos 或 ETCS
    字段。 *)

Program Definition Topos_HasInitial
  : HasInitial C
  :=
  {|hasOpTerminal :=
      {|Term := ToposInitial
      ; terminal_universal := topos_initial_universal
      |}
  |}.

(** The derived initial object is strict: every arrow into it is an
    isomorphism. Retain the already constructed outgoing universal arrow
    as the inverse; both laws use specified hom equality. *)

(** 推导出的始对象是严格的：每个指向它的箭头都是同构。保留已构造的出发泛
    箭头作为逆，两个定律均使用指定 Hom 相等。 *)

Definition topos_initial_strict {X : C} (f : Hom X ToposInitial)
  : is_iso f.
Proof.
  exists (topos_init X). split.
  - apply (bottom_true_hom_eq
      (bottom_true_comp topos_initial_bottom f)).
  - apply (bottom_true_hom_eq topos_initial_bottom).
Defined.

End ToposInitial.
