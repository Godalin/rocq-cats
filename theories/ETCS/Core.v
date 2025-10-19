From Cats Require Import Cat.Core.
From Cats Require Import Cat.Pullback.
From Cats Require Import ETCS.Nat.
From Cats Require Import ETCS.Sub.



(** Well-Pointed Category *)

Class IsWellPointed (C : Cat) `(!HasTerminal C) :=
  { axiom_well_pointed {X Y} {f g : Hom X Y}
    : ∀ x : Hom 1 X, f ∘ x ≈ g ∘ x → f ≈ g
  }.

Class HasAxiomChoice (C : Cat) :=
  { axiom_choice {X Y} {f : Hom X Y}
    : (* TODO surjection *) ∃ g, is_rinv_of f g
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
