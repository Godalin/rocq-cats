From Cats Require Import
  Instance.Set.Simplicial.Coskeletal
  Instance.Set.Simplicial.Vertex.Horn2
  Instance.Set.Simplicial.Cocycle.Kan
  Instance.Bool.Commutative.

(** Registered fixed-input interfaces can be composed without merging two
    deliberately distinct choices for the same horn. *)

Minks.Struct TwoHornSelections@{u p +}
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (n : nat) (i : Ordinal n)
  with  firstHorn : HasHornFillers [X, n, i],
        secondHorn : HasHornFillers [X, n, i].

Section SelectionRecovery.
Context {X : Fct (Δ^op) SetCat} {n : nat} {i : Ordinal n}
    (H K : HasHornFillers X n i).

Example first_selection_kept
  : TwoHornSelections_firstHorn X n i (MakeTwoHornSelections X n i H K) = H
  := eq_refl.

Example second_selection_kept
  : TwoHornSelections_secondHorn X n i (MakeTwoHornSelections X n i H K) = K
  := eq_refl.

End SelectionRecovery.

(** The full Kan family remains one selected component; its indexed
    members are obtained by the original projection. *)

Minks.Struct SelectedKan@{u p +}
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  with  kan : HasKanFillers [X].

Minks.Struct SelectedCoskeleton@{u p +}
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (k : nat)
  with  coskeleton : IsCoskeletal [X, k].

Minks.Struct SelectedLocalHorn (C : Cat) (i : Ordinal 2)
  with  localHorn : HasHorn2Fillers [C, i].

Section FamilyRecovery.
Context {X : Fct (Δ^op) SetCat} (K : HasKanFillers X)
    (n : nat) (i : Ordinal (S n)) (h : HornS X (S n) i).

Example selected_family_computes
  : @horn_fill X (S n) i
      (@hasHornFillers X (SelectedKan_kan X (MakeSelectedKan X K)) n i) h =
      @horn_fill X (S n) i (@hasHornFillers X K n i) h
  := eq_refl.

End FamilyRecovery.

(** Both strict carrier/equality orders remain available to every
    registered simplicial component, without a common resizing bound. *)

Section IndependentSizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
    (Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

Check TwoHornSelections X.
Check TwoHornSelections Y.
Check SelectedKan X.
Check SelectedKan Y.
Check SelectedCoskeleton X.
Check SelectedCoskeleton Y.

End IndependentSizes.


(** Complete shared coefficient bundles supply the existing operations
    and laws; no extra coefficient structure is introduced by the mixins. *)

Section PackedCoefficients.
Context (M : CommMonoid) (G : AbGroup).

Definition commutative_coefficients_model
  : Fct (Δ^op) SetCat
  := Z²(M).

Definition abelian_coefficients_Kan
  : HasKanFillers (Z²(G) : Fct (Δ^op) SetCat)
  := two_cocycle_HasKanFillers.

End PackedCoefficients.

Example boolean_group_parent_kept
  : AbGroupToGroup BoolS_AbGroup = BoolS_Group
  := eq_refl.
