From Cats Require Import Cat.Core.



(** Natural-Numbers Object *)

Class HasNNO `(C : Cat) :=
  { hasTerminal :: HasTerminal C
  ; NNO : Ob
  ; zero : Hom 1 NNO
  ; succ : Hom NNO NNO
  ; rec {X} : Hom 1 X → Hom X X → Hom NNO X

  ; axiom_nat_rec_proper {X}
    :: Proper (@HomEq[1, X] ==> @HomEq[X, X] ==> @HomEq[NNO, X]) rec

  ; axiom_naturals {X}
    : ∀ z : Hom 1 X, ∀ s : Hom X X,
        is_unique (λ f, f ∘ zero ≈ z ∧ f ∘ succ ≈ s ∘ f)
          (rec z s)
  }.
