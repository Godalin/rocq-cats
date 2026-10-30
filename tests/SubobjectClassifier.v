From Cats Require Import Cat.Core Cat.Set Cat.Pullback Cat.Morphism ETCS.Sub.
From CatsTests Require Import Pullback.

Section Classifier.
Context `{C : Cat} `{HT : !HasTerminal C} `{HC : !HasSubObjectClassifier C HT}.
Context {X Y : @Ob C} (m : X ↣ Y).

Example chosen_characteristic_square
  : is_pullback (χ m) truth X m !.
Proof. apply axiom_sub. Qed.

Example classifying_candidate_unique (c : Hom Y Ω)
    (Hc : is_pullback c truth X m !)
  : c ≈ χ m.
Proof. apply axiom_sub. exact Hc. Qed.

(** The selected square is not evidence that an arbitrary candidate
    classifies m. The old constant predicate accepted this application. *)
Fail Definition arbitrary_candidate_unique (c : Hom Y Ω) : c ≈ χ m :=
  that _ _ (axiom_sub (m := m)) c (this _ _ (axiom_sub (m := m))).

(** The derived characterization must also accept any terminal leg, not
    only the particular terminal morphism used by the chosen structure. *)
Example candidate_with_arbitrary_terminal_leg
    (c : Hom Y Ω) (a : Hom X 1) (Hc : is_pullback c truth X m a)
  : c ≈ χ m.
Proof.
  destruct (SubOC_subobject_classifier Y {| sub := X; sub_mono := m |})
    as [k [_ Hunique]].
  transitivity k.
  - apply Hunique. exists a. exact Hc.
  - symmetry. apply Hunique. exists !. apply axiom_sub.
Qed.

End Classifier.

(** A concrete distinction between the selected and a nonclassifying
    candidate: true classifies the identity of the singleton; false does not
    even give a commuting square with the same truth map. *)
Example singleton_identity_classifying_square
  : @is_pullback SetCat unit_setoid unit_setoid bool_setoid
      true_map true_map unit_setoid id_resp id_resp.
Proof.
  split. reflexivity.
  intros Q q1 q2 Hq. exists q1. split.
  - split; intros u. reflexivity.
    change (q1 u = q2 u). destruct (q1 u), (q2 u). reflexivity.
  - intros k [H1 H2] u. exact (H1 u).
Qed.

Example false_does_not_classify_singleton_identity
  : @is_pullback SetCat unit_setoid unit_setoid bool_setoid
      false_map true_map unit_setoid id_resp id_resp → Empty_set.
Proof. intros [Hcomm _]. specialize (Hcomm tt). discriminate Hcomm. Qed.

Print Assumptions SubOC_subobject_classifier.
Print Assumptions candidate_with_arbitrary_terminal_leg.
Print Assumptions singleton_identity_classifying_square.
Print Assumptions false_does_not_classify_singleton_identity.
