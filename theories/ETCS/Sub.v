From Cats Require Import Cat.Core Cat.Terminal Cat.Pullback Cat.Morphism.

(** * Sub-object Classifier

   sX ------> s0
    v          v
    |          |
    |          |
    |          |
    v          v
    X ------> SubOC *)

Section SubObjectClassifier.
Context {C : Cat}.

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

End SubObjectClassifier.

Class HasSubObjectClassifier (C : Cat) (HT : HasTerminal C) :=
  { SubOC : Ob
  ; truth : Hom 1 SubOC
  ; classifier_universal : is_subobject_classifier SubOC (term_Sub truth)
  }.

Arguments classifier_universal {_ _ _} _ _.

Definition char {C : Cat} `{HT : !HasTerminal C}
    `{HSC : !HasSubObjectClassifier C HT} {X Y} (m : X ↣ Y) : Hom Y SubOC :=
  (classifier_universal Y {| sub := X; sub_mono := m |}).1.

Notation Ω := SubOC.
Notation χ := char.

Theorem classifier_char_unique {C : Cat} `{HT : !HasTerminal C}
    `{HSC : !HasSubObjectClassifier C HT} {X Y} {m : Mono X Y}
  : is_unique (λ c, is_pullback c truth X m !) (χ m).
Proof.
  destruct (classifier_universal Y {| sub := X; sub_mono := m |}).2
    as [[a [Hcomm Hpb]] Hunique].
  split.
  - split.
    + rewrite <- (term_η a). exact Hcomm.
    + intros Q q1 q2 Hq.
      destruct (Hpb Q q1 q2 Hq) as [h [[H1 H2] Hu]].
      exists h. split.
      * split. exact H1. rewrite <- (term_η a). exact H2.
      * intros k [Hk1 Hk2]. apply Hu. split.
        exact Hk1. rewrite (term_η a). exact Hk2.
  - intros c Hc. apply Hunique. exists !. exact Hc.
Qed.
