From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Instance.Set.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  DTT.CwF
  DTT.Display.Section
  DTT.Context.Elements
  DTT.Context.PairComparison.

(** Substitution-term pair comparisons keep both Hom orders and fixed
    original type/term bounds above the base-law auxiliary universe. *)

Section CanonicalSubstitutionPairLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint l < a.
Constraint d < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
  (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition canonical_substitution_pair_high_eq_map
  := @context_elements_pair_resp C T HC.
Definition canonical_substitution_pair_low_eq_map
  := @context_elements_pair_resp D U HU.
Definition canonical_substitution_pair_high_eq_inv_map
  := @context_elements_pair_inv_resp C T HC.
Definition canonical_substitution_pair_low_eq_inv_map
  := @context_elements_pair_inv_resp D U HU.
Definition canonical_substitution_pair_high_eq_beta
  := @context_elements_pair_β C T HC.
Definition canonical_substitution_pair_low_eq_beta
  := @context_elements_pair_β D U HU.
Definition canonical_substitution_pair_high_eq_eta
  := @context_elements_pair_η C T HC.
Definition canonical_substitution_pair_low_eq_eta
  := @context_elements_pair_η D U HU.
Definition canonical_substitution_pair_high_eq_sub
  := @context_elements_pair_sub C T HC.
Definition canonical_substitution_pair_low_eq_sub
  := @context_elements_pair_sub D U HU.
Definition canonical_substitution_pair_high_eq_inv_sub
  := @context_elements_pair_inv_sub C T HC.
Definition canonical_substitution_pair_low_eq_inv_sub
  := @context_elements_pair_inv_sub D U HU.
End CanonicalSubstitutionPairLevels.
