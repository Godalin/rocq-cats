From Cats Require Import Cat.Core.
From Cats Require Import Cat.Pullback.
From Cats Require Import ETCS.Nat.
From Cats Require Import ETCS.Sub.



(** Well-Pointed Category *)

Class IsWellPointed (C : Cat) `(!HasTerminal C) :=
  { axiom_well_pointed {X Y} {f g : Hom X Y}
    : f ≉ g → ∃ x : Hom 1 X,
      f ∘ x ≉ g ∘ x
  }.

Class HasAxiomChoice (C : Cat) :=
  { axiom_choice {X Y} {f : Hom X Y}
    : (* TODO surjection *) ∃ g, is_rinv_of f g
  }.

Class ETCS (C : Cat) :=
  { hasTerminal :: HasTerminal C
  ; hasProduct :: HasProduct C
  ; hasExponential :: HasExponential hasProduct
  ; hasPullback :: HasPullback C
  ; hasSubObjectClassifier
    :: HasSubObjectClassifier C hasTerminal
  ; isWellPointed :: IsWellPointed C hasTerminal
  ; hasAxiomChoice :: HasAxiomChoice C
  ; hasNNO :: HasNNO C
  }.



Section ETCS.
Context {C : Cat} `{E : !ETCS C}.

(** Let's do _Set Theory_ (in ETCS) ! *)

End ETCS.
