From Cats Require Import Cat.Core.



(** Natural-Numbers Object *)

Definition is_natural_numbers_object {C : Cat} `{!HasTerminal C}
    (N : Ob) (z : Hom 1 N) (s : Hom N N) :=
  ∀ X (z' : Hom 1 X) (s' : Hom X X),
    ∃ r : Hom N X,
      is_unique (λ r, r ∘ z ≈ z' ∧ r ∘ s ≈ s' ∘ r) r.

Class HasNaturalNumbersObject `(C : Cat) `(!HasTerminal C) :=
  { NNO : Ob
  ; zero : Hom 1 NNO
  ; succ : Hom NNO NNO
  ; nno_universal : is_natural_numbers_object NNO zero succ
  }.

Arguments nno_universal {_ _ _} _ _ _.

Definition rec {C : Cat} `{HT : !HasTerminal C}
    `{!HasNaturalNumbersObject C HT} {X}
    (z : Hom 1 X) (s : Hom X X) : Hom NNO X :=
  (nno_universal X z s).1.

Theorem nno_rec_unique {C : Cat} `{HT : !HasTerminal C}
    `{!HasNaturalNumbersObject C HT} {X} (z : Hom 1 X) (s : Hom X X)
  : is_unique (λ f, f ∘ zero ≈ z ∧ f ∘ succ ≈ s ∘ f) (rec z s).
Proof. exact (nno_universal X z s).2. Qed.

Global Instance nno_rec_proper {C : Cat} `{HT : !HasTerminal C}
    `{!HasNaturalNumbersObject C HT} {X}
  : Proper (@HomEq[1, X] ==> @HomEq[X, X] ==> @HomEq[NNO, X]) rec.
Proof.
  intros z z' Hz s s' Hs.
  destruct (nno_rec_unique z s) as [[H0 Hsucc] _].
  apply (nno_rec_unique z' s'). split.
  - transitivity z; assumption.
  - transitivity (s ∘ rec z s). exact Hsucc. apply comp_r. exact Hs.
Qed.
