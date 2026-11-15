From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Preorder
  Cat.Terminal
  Cat.Pullback
  Cat.Morphism
  Topos.Sub
  Topos.Representation
  Topos.PredicateOrder.

(** * Classifier Predicates as Thin Categories

    Fix named terminal, classifier and pullback choices. Reuse the
    transparent entailment preorder as a category whose arrows retain
    classified-subobject factors. Substitution induces functors;
    no product or exponential choice is needed. *)

(** * 分类子谓词的薄范畴

    固定具名终对象、分类子及拉回选择。将透明蕴含预序复用为范畴，其箭头保留
    分类子对象因子。代入诱导函子，不需要积或指数选择。 *)

Section PredicateCategories.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{PB : !HasPullback C}.

(** Predicates on a fixed context form the existing thin preorder model.
    Its identity and composition retain the transparent original factors. *)

(** 固定上下文上的谓词形成既有薄预序模型；恒等与复合保留透明的原有因子。 *)

Definition PredicateCat (X : C)
  : Cat
  := @PreorderCat _ (@predicate_le C HT HC PB X) (PredicatePreorder X).

(** Substitution acts on predicates and on their actual entailment factors
    through the previously proved inverse-image monotonicity. *)

(** 代入通过已有逆像单调性作用于谓词及其实际蕴含因子。 *)

Definition PredicateReindexF {X Y : C} (k : Hom X Y)
  : Fct (PredicateCat Y) (PredicateCat X)
  := @PreorderF _ _ _ _ (PredicatePreorder Y) (PredicatePreorder X)
      (λ f, f ∘ k) (λ f g H, predicate_le_subst k H).

(** Identity substitution preserves each predicate by its specified
    classifier-arrow equality, without equating selected factor records. *)

(** 恒等代入按分类箭头的指定相等保持每个谓词，不识别选定因子记录。 *)

Theorem predicate_reindex_id {X : C} (f : Hom X Ω)
  : PredicateReindexF id f ≈ f.
Proof. apply comp_id_r. Qed.

(** Context substitution composes contravariantly up to that same equality.
    This is an object-map law, not native equality of chosen functors. *)

(** 上下文代入按同一相等逆变复合；这是对象映射定律，不是选定函子的原生相等。 *)

Theorem predicate_reindex_comp {X Y Z : C} (k : Hom X Y) (l : Hom Y Z)
    (f : Hom Z Ω)
  : PredicateReindexF k (PredicateReindexF l f)
    ≈ PredicateReindexF (l ∘ k) f.
Proof. apply comp_assoc. Qed.

End PredicateCategories.
