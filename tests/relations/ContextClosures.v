From Cats.Set.Relation Require Import Congruence.

(** * Indexed Context Closure Regressions *)

Local Open Scope relation_scope.

Section IndependentLevels.
Universes i a o r.
Constraint a < o.
Constraint o < r.
Constraint i < r.
Context (I : Type@{i}) (A : I → Type@{a}).
Context (K : ContextSystem@{i a o} A).
Context (R : RelationFamily@{i a r _} A).

(** Carrier, operation and witness levels must stay distinct when the
    generated closures are packaged as endomorphisms of relation families. *)

Definition separated_compatible_closure
  : Clos (λ R S : RelationFamily@{i a r _} A, R ⊆ᵢ S)
  := CompatibleClosOp K.

Definition separated_congruence_closure
  : Clos (λ R S : RelationFamily@{i a r _} A, R ⊆ᵢ S)
  := CongruenceClosOp K.

(** The equivalence instance must apply to the original carrier level,
    rather than silently lifting the carrier to the edge-witness level. *)

Definition separated_generated_equivalence (j : I)
  : Equivalence (EquivClosOp@{a r _} (A j) (R j))
  := EquivClosOp_Equivalence (R j).

Definition separated_interchange
  : (R^≈ᵢ)^C[K] ⊆ᵢ (R^C[K])^≈ᵢ
  := compatible_equivalence_interchange K R.

Definition separated_joint_presentation
  : EquationalClos K R ≈ᵢ (R^C[K])^≈ᵢ
  := equational_closure_paths K R.

Definition separated_congruence_universal
    (S : RelationFamily@{i a r _} A)
    (hs : is_compatible K S) (es : ∀ j, Equivalence (S j))
  : CongruenceClosOp K R ⊆ᵢ S ↔ R ⊆ᵢ S
  := congruence_closure_universal K R S hs es.

End IndependentLevels.

Section LargerIndices.
Universes i a r.
Constraint a < r.
Constraint r < i.
Context (I : Type@{i}) (A : I → Type@{a}).

(** Pointwise paths store no index, so their witness bound need not
    contain the index universe. Context iteration has a different bound. *)

Definition large_index_pointwise_closure
  : Clos (λ R S : RelationFamily@{i a r _} A, R ⊆ᵢ S)
  := FamilyEquivClosOp A.

End LargerIndices.

Section SmallerGenerators.
Universes i a o r p.
Constraint r < a.
Constraint a < o.
Constraint o < i.
Constraint i < p.
Context (I : Type@{i}) (A : I → Type@{a}).
Context (K : ContextSystem@{i a o} A).
Context (R : RelationFamily@{i a r _} A).

(** The raw context construction can use small generators and retain
    contexts in a separately chosen, larger witness universe. *)

Definition small_generator_context_closure
  : RelationFamily@{i a p _} A
  := ContextClos K R.

End SmallerGenerators.

Section IndexedComputations.

(** The two fibers have different carriers. Pairing changes the index,
    and its label stores the argument that remains fixed. *)

Inductive ValueSort
  : Type
  :=| scalar | tuple.

Definition Values (i : ValueSort)
  : Type
  := match i with scalar => nat | tuple => (nat * nat)%type end.

Inductive PairOperation
  : ValueSort → ValueSort → Type
  :=| pair_left (n : nat) : PairOperation scalar tuple
    | pair_right (n : nat) : PairOperation scalar tuple.

Program Definition PairContexts
  : ContextSystem Values
  :=
  {|context_operation := PairOperation
  ; context_action i j c :=
      match c in PairOperation s t return Values s → Values t with
      | pair_left n => λ x, (x, n)
      | pair_right n => λ x, (n, x)
      end
  |}.

(** Only the scalar fiber has generators. Each edge increments a number
    and stores a natural-number payload, independent of that endpoint. *)

Inductive Increment
  : RelationFamily Values
  :=| increment (n w : nat) : Increment scalar n (S n).

Definition increment_weight {i} {x y : Values i} (p : Increment i x y)
  : nat
  := match p with increment _ w => w end.

(** A compatible equivalence target observes the sum of edge payloads. *)

Definition WeightRelation (i : ValueSort) (_ _ : Values i)
  : Type
  := nat.

Local Program Instance weight_relation_Equivalence (i : ValueSort)
  : Equivalence (WeightRelation i)
  :=
  {|Equivalence_Reflexive x := 0
  ; Equivalence_Symmetric x y p := p
  ; Equivalence_Transitive x y z p q := (p + q)%nat
  |}.

Definition weight_relation_compatible
  : is_compatible PairContexts WeightRelation
  := λ i j c x y p, p.

Definition context_weight
  : Increment^C[PairContexts] ⊆ᵢ WeightRelation
  := context_closure_preserves PairContexts weight_relation_compatible
      (λ i x y p, increment_weight p).

Definition zigzag_weight {i} {x y : Values i}
    (p : (Increment^C[PairContexts])^≈ᵢ i x y)
  : nat
  := equivalence_closure_preserves (S := WeightRelation i)
      (λ x, x) (context_weight i) p.

(** A reverse scalar edge lifts to a reverse tuple edge. The interchange
    witness must compute across the change of carrier. *)

Example indexed_interchange_computes
  : zigzag_weight
      (compatible_equivalence_interchange PairContexts Increment
        tuple (4, 1) (4, 0)
        (context_lift (K := PairContexts) (pair_right 4)
          (context_step
            (rtc_step (R := (Increment scalar)^±)
              (x := 1) (y := 0) (inr (increment 0 7)))))) = 7.
Proof. reflexivity. Qed.

(** Replace the two arguments separately, then concatenate. This obtains
    binary congruence from operations with exactly one varying input. *)

Definition both_pair_arguments
  : EquationalClos PairContexts Increment tuple (0, 0) (1, 1)
  := equation_trans
      (equation_context (K := PairContexts)
        (pair_left 0) (equation_step (increment 0 2)))
      (equation_context (K := PairContexts)
        (pair_right 1) (equation_step (increment 0 3))).

Example joint_to_paths_computes
  : zigzag_weight
      (fst (equational_closure_paths PairContexts Increment
        tuple (0, 0) (1, 1)) both_pair_arguments) = 5.
Proof. reflexivity. Qed.

(** Folding the reverse comparison retains the same observable payload,
    without asserting an inverse equation on the derivation itself. *)

Example joint_paths_roundtrip_computes
  : equational_closure_preserves PairContexts weight_relation_compatible
      weight_relation_Equivalence (λ i x y p, increment_weight p)
      tuple (0, 0) (1, 1)
      (snd (equational_closure_paths PairContexts Increment
        tuple (0, 0) (1, 1))
        (fst (equational_closure_paths PairContexts Increment
          tuple (0, 0) (1, 1)) both_pair_arguments)) = 5.
Proof. reflexivity. Qed.

End IndexedComputations.
