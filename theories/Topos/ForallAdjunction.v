From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Preorder
  Cat.Natural
  Cat.Adjunction
  Cat.Logic.Adjunction
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Pullback
  Cat.Morphism
  Topos.Sub
  Topos.Representation
  Topos.PredicateOrder
  Topos.PredicateCategory
  Topos.Forall.

(** * Projection Quantification as an Actual Adjunction

    Fix named terminal, classifier, pullbacks, products and relative
    exponentials. Apply the general preorder bridge to the already proved
    Type-valued correspondence. Quantification and transposes retain the
    original choices and factors; no second universal proof is selected. *)

(** * 作为实际伴随的投影量化

    固定具名终对象、分类子、拉回、积及相对指数。将一般预序桥梁应用于已证明
    的 Type 值对应；量化与转置保留原有选择和因子，不另选一套泛性质证明。 *)

Section ForallAdjunction.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier C HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** The chosen projection quantifier is monotone by the existing theorem.
    Keep this exact arrow map in the induced preorder functor. *)

(** 选定投影量词由已有定理给出单调性，诱导的预序函子保留同一箭头映射。 *)

Definition PredicateForallF (A X : C)
  : Fct (PredicateCat (X × A)) (PredicateCat X)
  := @PreorderF _ _ _ _ (PredicatePreorder (X × A)) (PredicatePreorder X)
      (forall_predicate A) (λ f g H, predicate_forall_mono A H).

(** Assemble the actual right adjunction to projection substitution with
    the integrated generic bridge and the existing factor correspondence. *)

(** 用已集成的一般桥梁及既有因子对应，组装沿投影代入的实际右伴随。 *)

Definition PredicateForallAdj (A X : C)
  : PredicateReindexF (π1 : Hom (X × A) X) ⊣ PredicateForallF A X
  := PreorderAdj (PredicateReindexF π1) (PredicateForallF A X)
      (λ r f, predicate_forall_universal A r f).

(** Forward transposition preserves the original quantified factor. *)

(** 正向转置保留原有量化因子。 *)

Definition predicate_forall_adjunct_data (A : C) {X : C}
    (r : Hom X Ω) (f : Hom (X × A) Ω) (H : r ∘ π1 ⊢Ω f)
  : adjunct (PredicateForallAdj A X) H
    = fst (predicate_forall_universal A r f) H
  := eq_refl.

(** Reverse transposition preserves the original weakening factor. *)

(** 反向转置保留原有弱化因子。 *)

Definition predicate_forall_unadjunct_data (A : C) {X : C}
    (r : Hom X Ω) (f : Hom (X × A) Ω) (H : r ⊢Ω ∀Ω[A] f)
  : unadjunct (PredicateForallAdj A X) H
    = snd (predicate_forall_universal A r f) H
  := eq_refl.

(** The unit is the original forward factor applied to the weakened
    predicate's transparent identity factor. *)

(** 单位是原有正向对应作用于弱化谓词的透明恒等因子。 *)

Definition predicate_forall_unit_data (A : C) {X : C} (r : Hom X Ω)
  : adj_unit (PredicateForallAdj A X) r
    = fst (predicate_forall_universal A r (r ∘ π1))
        (predicate_le_refl (r ∘ π1))
  := eq_refl.

(** The counit is exactly the previously defined quantifier evaluation. *)

(** 余单位恰好是先前定义的量词求值。 *)

Definition predicate_forall_counit_data (A : C) {X : C}
    (f : Hom (X × A) Ω)
  : adj_counit (PredicateForallAdj A X) f = predicate_forall_eval A f
  := eq_refl.

End ForallAdjunction.
