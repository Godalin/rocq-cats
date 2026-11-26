From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Equalizer
  Cat.Pullback
  Cat.Morphism
  Cat.SubobjectIntersection
  Topos.Sub
  Topos.Representation
  Topos.Conjunction
  Topos.PredicateOrder
  Topos.Implication.

(** * Exchange and Truth for Implication

    Reuse the conjunction adjunction to exchange two antecedents and
    eliminate a true antecedent. These laws do not require exponentials. *)

(** * 蕴含的交换与真

    复用合取伴随交换两个前件并消去真前件；这些定律不要求指数。 *)

Section ImplicationLaws.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HE : !HasEqualizer C}.

(** Exchange two antecedents using commutativity of their conjunction.
    Both directions return actual classified-subobject factors. *)

(** 通过前件合取的交换性交换两个前件；两个方向均返回实际分类子对象因子。 *)

Definition predicate_implication_exchange {X : C} (r s t : Hom X Ω)
  : r ⊢Ω s ⇒Ω t ↔ s ⊢Ω r ⇒Ω t.
Proof.
  pose (R := predicate_implication_universal r s t).
  pose (S := predicate_implication_universal s r t).
  pose (E := classified_sub_congr (conjunction_comm r s)). split.
  - intros H. exact (fst S (sub_factor_comp (snd E) (snd R H))).
  - intros H. exact (fst R (sub_factor_comp (fst E) (snd S H))).
Defined.

(** A true antecedent leaves its consequent unchanged, with respect to
    the specified equality of classifier arrows. *)

(** 相对于分类箭头的指定相等，真前件不改变其后件。 *)

Theorem implication_truth {X : C} (f : Hom X Ω)
  : (truth ∘ !) ⇒Ω f ≈ f.
Proof.
  apply (fst (predicate_le_eq _ _)). split.
  - exact (sub_factor_comp
      (snd (classified_sub_congr (conjunction_top ((truth ∘ !) ⇒Ω f))))
      (predicate_implication_eval (truth ∘ !) f)).
  - exact (fst (predicate_implication_universal f (truth ∘ !) f)
      (predicate_conjunction_left f (truth ∘ !))).
Qed.

End ImplicationLaws.
