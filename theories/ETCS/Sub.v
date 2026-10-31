From Cats Require Import Cat.Core Cat.Pullback Cat.Morphism.

(** * Sub-object Classifier

   sX ------> s0
    v          v
    |          |
    |          |
    |          |
    v          v
    X ------> SubOC *)

Class HasSubObjectClassifier `(C : Cat) `(!HasTerminal C) :=
  { SubOC : Ob
  ; truth : Hom 1 SubOC
  ; char {X Y} : X ↣ Y → Hom Y SubOC

  ; classifier_char_unique {X Y} {m : Mono X Y}
    : is_unique (λ c, is_pullback c truth X m !) (char m)
  }.

Notation Ω := SubOC.
Notation χ := char.

Section SubObjectClassifier.
Context `{C : Cat}.

Definition is_subobject_classifier (Ω : Ob) (Ω0 : Sub Ω)
  := ∀ A (A0 : Sub A), ∃ χ,
    is_unique (λ χ, ∃ a, is_pullback χ Ω0 A0 A0 a) χ.

Proposition sub_subobject_1 {Ω : Ob} {Ω0 : Sub Ω}
  : is_subobject_classifier Ω Ω0
    → is_terminal Ω0.
Proof. unfold is_subobject_classifier. intros HSubOC.
  intro A. specialize (HSubOC A id).
  destruct HSubOC as [χ [[v H1] H2]].
  exists v. split. auto. intros u _.
  destruct H1 as [H1 H3].
  assert (H4 : ∃ a, is_pullback (Ω0 ∘ u) Ω0 A id a).
  { exists u. split. cato. intros. exists q1.
    rewrite comp_assoc in X.
    apply sub_mono in X. split; cato.
    intros h [H4 H5]. rewrite comp_id_l in H4. cato. }
  specialize (H2 (Ω0 ∘ u) H4).
  apply (sub_mono _ Ω0).
  rewrite H2. rewrite comp_id_r in H1. rewrite H1.
  reflexivity.
Qed.



Context `{!HasTerminal C}.
Context `{!HasSubObjectClassifier C _}.

Theorem SubOC_subobject_classifier
  : is_subobject_classifier Ω truth.
Proof. intros A A0.
  destruct (classifier_char_unique (m := A0)) as [Hchar Hunique].
  exists (χ A0). split.
  - exists !. exact Hchar.
  - intros c [a [Hcomm Hpb]]. apply Hunique. split.
    + rewrite <- (term_η a). exact Hcomm.
    + intros Q q1 q2 Hq.
      destruct (Hpb Q q1 q2 Hq) as [h [[H1 H2] Hu]].
      exists h. split.
      * split. exact H1. rewrite <- (term_η a). exact H2.
      * intros k [Hk1 Hk2]. apply Hu. split.
        exact Hk1. rewrite (term_η a). exact Hk2.
Qed.

End SubObjectClassifier.
