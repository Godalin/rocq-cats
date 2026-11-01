From Cats Require Import Cat.Core Cat.Terminal Cat.Product Cat.Exponential.
From Cats Require Import Cat.Morphism.
From Cats Require Import Cat.Pullback.
From Cats Require Import ETCS.Nat.
From Cats Require Import ETCS.Sub.



(** Well-Pointed Category: equality on all global points detects equality. *)

Class IsWellPointed (C : Cat) (HT : HasTerminal C) :=
  { well_pointed_ext {X Y} {f g : Hom X Y}
    : (∀ x : Hom 1 X, f ∘ x ≈ g ∘ x) → f ≈ g
  }.

(** Choice for ETCS models: every epimorphism has a right inverse. *)

Class HasAxiomChoice (C : Cat) :=
  { choice_split_epi {X Y} {f : Hom X Y}
    : is_epi f → ∃ g, is_rinv_of f g
  }.

Class ETCS (C : Cat) :=

  (** [ETCS] is based on a _elementary topos_ *)

  { hasTerminal :: HasTerminal C
  ; hasInitial :: HasInitial C
  ; hasProduct :: HasProduct C
  ; hasExponential :: HasExponential hasProduct
  ; hasPullback :: HasPullback C
  ; hasSubObjectClassifier
    :: HasSubObjectClassifier C hasTerminal

  (** ... with other three axioms *)

  ; isWellPointed :: IsWellPointed C hasTerminal
  ; hasAxiomChoice :: HasAxiomChoice C
  ; hasNaturalNumbersObject
    :: HasNaturalNumbersObject C hasTerminal
  }.



Declare Scope etcs_scope.
Open Scope etcs_scope.

Notation "'∅'" := Init.

Notation "'∈' X" := (Hom 1 X)
  (at level 35) : etcs_scope.

Section ETCS.
Context {C : Cat} `{Axioms : !ETCS C}.

(** Let's do _Set Theory_ (in [ETCS]) ! *)

(** ** Empty Set *)

(* Proposition init_no_elem
  : ∈ 0 → Empty_set.
Proof. intros x. *)

End ETCS.
