From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Pullback
  Topos.Nat
  Topos.ETCS.

(** * Shared components in Topos and ETCS

    Assemble only the supplied choices. Generated parent views and inferred
    mixins must read exactly those stored components. *)

Section Assembly.
Context (D : CCC) (PB : HasPullback D)
  (SC : HasSubObjClassifier (hasTerminal D)).

Definition selected_topos
  : Topos
  := ToposOfCCC D PB SC.

Example same_terminal
  : hasTerminal (ToposToCCC selected_topos) = hasTerminal D
  := eq_refl.
Example same_products
  : hasProduct (ToposToCCC selected_topos) = hasProduct D
  := eq_refl.
Example same_exponentials
  : hasExponential (ToposToCCC selected_topos) = hasExponential D
  := eq_refl.
Example same_pullbacks
  : hasPullback selected_topos = PB
  := eq_refl.
Example same_classifier
  : hasSubObjClassifier selected_topos = SC
  := eq_refl.

Context (I : HasInitial D) (W : IsWellPointed (hasTerminal D))
  (A : HasAxiomChoice D) (N : HasNaturalNumbersObj (hasTerminal D)).

Definition selected_etcs
  : ETCS
  := ETCSOfTopos selected_topos I W A N.

Example inherited_terminal
  : hasTerminal (ToposToCCC (ETCSToTopos selected_etcs)) = hasTerminal D
  := eq_refl.
Example inherited_classifier
  : hasSubObjClassifier (ETCSToTopos selected_etcs) = SC
  := eq_refl.
Example same_initial
  : hasInitial selected_etcs = I
  := eq_refl.
Example same_well_pointedness
  : isWellPointed selected_etcs = W
  := eq_refl.
Example same_choice
  : hasAxiomChoice selected_etcs = A
  := eq_refl.
Example same_natural_numbers
  : hasNaturalNumbersObj selected_etcs = N
  := eq_refl.

End Assembly.

(** A bare topos selects neither choice nor natural numbers. *)

Fail Definition unchosen_choice (C : Topos)
  : HasAxiomChoice C
  := ltac:(typeclasses eauto).
Fail Definition unchosen_natural_numbers (C : Topos)
  : HasNaturalNumbersObj (hasTerminal C)
  := ltac:(typeclasses eauto).

(** Instance search agrees by conversion with the chosen bundle fields. *)

Definition inferred_classifier (C : ETCS)
  : HasSubObjClassifier (hasTerminal C)
  := ltac:(typeclasses eauto).
Example inferred_same_classifier (C : ETCS)
  : inferred_classifier C = hasSubObjClassifier (ETCSToTopos C)
  := eq_refl.

Definition inferred_recursion (C : ETCS)
  : HasNaturalNumbersObj (hasTerminal C)
  := ltac:(typeclasses eauto).
Example inferred_same_recursion (C : ETCS)
  : inferred_recursion C = hasNaturalNumbersObj C
  := eq_refl.

(** Rewrite through recursion and composition using the derived Proper
    instance, without adding respectfulness to the NNO interface. *)

Lemma recursion_rewriting (C : ETCS) {X Y : C}
    (z z' : Hom 1 X) (s s' : Hom X X) (k : Hom X Y)
    (Hz : z ≈ z') (Hs : s ≈ s')
  : k ∘ rec z s ≈ k ∘ rec z' s'.
Proof. rewrite Hz, Hs. reflexivity. Qed.
