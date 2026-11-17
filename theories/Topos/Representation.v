From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Pullback
  Cat.Morphism
  Cat.Functor.Core
  Cat.Natural
  Topos.Sub
  Instance.Set.Core
  Instance.Set.Subobject
  Instance.Set.Lift
  Instance.Set.Representable.

(** * Representing Subobjects by Truth Values

    The truth subobject is a universal element of the subobject functor.
    Apply the general universal-element theorem in the opposite category;
    no second proof of naturality or inverse naturality is required. *)

(** * 以真值表示子对象

    真子对象是子对象函子的泛元素。在反范畴中应用一般泛元素定理，
    无须另证自然性或逆的自然性。 *)

(** ** Classifying Inverse Images

    Fix a chosen terminal object, classifier and pullbacks in [C]. Pulling
    back truth reconstructs a subobject from a characteristic arrow. The
    two round trips use hom equality and subobject equivalence, respectively,
    rather than equality of representatives or proof records. *)

(** ** 分类逆像

    在 [C] 中固定选定终对象、分类子和拉回。拉回真子对象即可由特征箭头重构
    子对象；两个往返分别使用 Hom 相等及子对象等价，不比较表示或证明记录。 *)

Section ClassifyingInverseImages.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HSC : !HasSubObjClassifier C HT} `{HPb : !HasPullback C}.

(** The subobject classified by [f] is the selected inverse image of truth. *)

(** 由 [f] 分类的子对象是真子对象的选定逆像。 *)

Definition ClassifiedSub {X : @Ob C} (f : Hom X Ω)
  : Sub X
  := Sub_fmap f (term_Sub truth).

(** Equality of classifying arrows gives equivalent inverse images. *)

(** 相等的分类箭头给出等价逆像。 *)

Global Instance ClassifiedSub_proper {X : @Ob C}
  : Proper (@HomEq[X, Ω] ==> Sub_eq X) ClassifiedSub.
Proof.
  intros f g H.
  exact (fct_fmap_proper (C^op) SetCat (@SubF C HPb)
    f g H (term_Sub truth)).
Qed.

(** Classifying the inverse image of truth recovers the supplied arrow. *)

(** 分类真子对象的逆像，恢复原箭头。 *)

Theorem classified_sub_char {X : @Ob C} (f : Hom X Ω)
  : χ (sub_mono _ (ClassifiedSub f)) ≈ f.
Proof.
  transitivity (χ (Mono_term truth) ∘ f).
  - exact (classifier_char_pullback f (Mono_term truth)
      (sub_mono _ (ClassifiedSub f)) (pb2 f truth) pullback_universal).
  - rewrite classifier_char_truth, comp_id_l. reflexivity.
Qed.

(** Pulling back truth along the characteristic arrow recovers the original
    subobject up to mutual factorization. *)

(** 沿特征箭头拉回真子对象，在相互分解等价下恢复原子对象。 *)

Definition classified_char_sub {X : @Ob C} (s : Sub X)
  : ClassifiedSub (χ (sub_mono _ s)) ~Sub s.
Proof.
  apply (snd (classifier_char_subobject_eq _ _)).
  apply classified_sub_char.
Defined.

End ClassifyingInverseImages.

(** ** The Generic Truth Subobject

    Raise subobject values and native representing hom-sets to independent
    ambient carrier and equality universes [u], [p]. This uses [Rep↑] on
    [C^op], so the represented arrows are ordinary arrows into the truth-value
    object of [C]. No
    resizing or equality between native universe levels is assumed. *)

(** ** 泛真子对象

    将子对象值及原生表示 Hom 广集提升到独立的环境载体／相等宇宙 [u]、[p]。
    在 [C^op] 上使用 [Rep↑]，表示箭头即 [C] 中指向真值对象的普通箭头。
    不假定大小重设或
    原生宇宙层级相等。 *)

Section SubobjectRepresentations.
Universe u p.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HSC : !HasSubObjClassifier C HT} `{HPb : !HasPullback C}.

(** Every subobject is a unique substitution of truth. The unique mediator
    is its already chosen characteristic arrow. *)

(** 每个子对象都是真子对象的唯一替换；唯一中介即已有的选定特征箭头。 *)

Definition classifier_truth_universal
  : @is_universal_element (C^op)
      (LiftF ∘F @SubF C HPb : Fct (C^op) SetCat@{u p _ _ _ _ _})
      (@SubOC C HT HSC) {|lower := @term_Sub C HT _ (@truth C HT HSC)|}.
Proof.
  intros X [s]. exists (χ (sub_mono _ s)).
  refine {|this := _
          ; that := _
          |}.
  - exact {|lower := classified_char_sub s|}.
  - intros f Hf.
    change ((@Hom C) X (@SubOC C HT HSC)) in f.
    change (@HomEq C X (@SubOC C HT HSC) f (χ (sub_mono _ s))).
    transitivity (χ (sub_mono _ (@ClassifiedSub C HT HSC HPb X f))).
    + symmetry. exact (@classified_sub_char C HT HSC HPb X f).
    + exact (classifier_char_subobject_proper _ _ (lower Hf)).
Defined.

(** The classifier represents the existing subobject functor. The general
    representation theorem supplies the natural map and its transparent
    inverse, without adding a choice of a concrete topos model. *)

(** 分类子表示已有子对象函子。一般表示定理提供自然映射及其透明逆，
    不额外选择任何具体拓扑斯模型。 *)

Definition SubobjectRepresentation
  : (@SubOC C HT HSC) ⦂ Rep↑ (
      LiftF ∘F @SubF C HPb : Fct (C^op) SetCat@{u p _ _ _ _ _})
  := universal_element_lifted_representation
      (LiftF ∘F @SubF C HPb : Fct (C^op) SetCat@{u p _ _ _ _ _})
      (X := (@SubOC C HT HSC))
      (x := {|lower := @term_Sub C HT _ (@truth C HT HSC)|})
      classifier_truth_universal.

(** A representation component pulls back truth along its supplied arrow. *)

(** 表示的分量沿给定箭头拉回真子对象。 *)

Theorem subobject_representation_at {X : @Ob C}
    (f : Hom X (@SubOC C HT HSC))
  : lower (SubobjectRepresentation.1 X
      {|lower := f|}) ~Sub ClassifiedSub f.
Proof. reflexivity. Qed.

(** The inverse component returns the chosen characteristic arrow, inside
    the explicit ambient-size wrapper. *)

(** 逆分量在显式环境大小包装内返回选定特征箭头。 *)

Theorem subobject_representation_inverse {X : @Ob C} (s : Sub X)
  : lower ((SubobjectRepresentation.2 X).1 {|lower := s|})
      ≈ χ (sub_mono _ s).
Proof. reflexivity. Qed.

End SubobjectRepresentations.
