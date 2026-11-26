From Cats.Set.Relation Require Import Equivalence.
From Cats.Set Require Import Generated.

(** * Relation Closure Interface Regressions

    These checks separate carrier, edge and path universes, then observe
    data carried through the generic closure laws and the legacy interface.
    They do not require equality between different derivations. *)

Local Open Scope relation_scope.
Local Open Scope set_scope.

Section LargerWitnesses.
Universes a r.
Constraint a < r.
Context (A : Type@{a}) (R : A → A → Type@{r}).

(** The chosen endomorphisms retain a witness bound strictly above the
    carrier. In particular, their packaging must not identify these levels. *)

Definition large_witness_path_closure
  : Clos (@subrelation@{a r r} A)
  := ReflTransClosOp A.

Definition large_witness_equivalence_closure
  : Clos (@subrelation@{a r r} A)
  := EquivClosOp A.

Definition large_witness_equivalence_comparison
  : R^±* ≈R R^≈
  := equivalence_closure_legacy R.

End LargerWitnesses.

Section SmallerEdges.
Universes a r p.
Constraint r < a.
Constraint a < p.
Context (A : Type@{a}) (R : A → A → Type@{r}).

(** Symmetry needs no carrier-sized witness, whereas paths may retain
    intermediate elements in a third, larger universe. *)

Definition small_witness_symmetric_closure
  : Clos (@subrelation@{a r r} A)
  := SymClosOp A.

Definition small_edges_large_paths
  : A → A → Type@{p}
  := @ReflTransClos@{a r p} A R.

Definition small_edges_large_path_step {x y : A} (h : R x y)
  : small_edges_large_paths x y
  := rtc_step h.

End SmallerEdges.

Section WitnessComputations.

(** A relation whose witnesses are observable natural numbers. Composition
    adds the numbers, and the empty path contributes zero. *)

Definition WeightedRelation (_ _ : bool)
  : Type
  := nat.

Local Program Instance weighted_relation_PreOrder
  : PreOrder WeightedRelation
  :=
  {|PreOrder_Reflexive x := 0
  ; PreOrder_Transitive x y z h k := (h + k)%nat
  |}.

(** Fold oriented paths without discarding either orientation's payload. *)

Definition path_weight {x y : bool} (p : WeightedRelation^±* x y)
  : nat
  := rtc_preserves (S := WeightedRelation) (λ x, x)
      (λ x y h, match h with inl n => n | inr n => n end) p.

Definition weighted_path
  : WeightedRelation^±* false true
  := rtc_trans
      (rtc_step (R := WeightedRelation^±) (x := false) (y := true) (inl 2))
      (rtc_step (R := WeightedRelation^±) (x := true) (y := true) (inr 3)).

(** Generic inflation and flattening must compute through the explicitly
    chosen inclusion preorder and the composite closure construction. *)

Example equivalence_inflation_computes
  : path_weight
      (closure_inflate (EquivClosOp bool) WeightedRelation
        false true 7) = 7.
Proof. reflexivity. Qed.

Example equivalence_flattening_computes
  : path_weight
      (closure_flatten (EquivClosOp bool) WeightedRelation
        true false
        (rtc_step (R := WeightedRelation^±*^±)
          (x := true) (y := false) (inr weighted_path))) = 5.
Proof. reflexivity. Qed.

(** Comparing with the existing derivation-tree interface also preserves
    the payload through both transparent witness transformations. *)

Example legacy_comparison_computes
  : path_weight
      (snd (equivalence_closure_legacy WeightedRelation false true)
        (fst (equivalence_closure_legacy WeightedRelation false true)
          weighted_path)) = 5.
Proof. reflexivity. Qed.

End WitnessComputations.
