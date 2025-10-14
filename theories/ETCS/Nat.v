From Cats Require Import Cat.Core.

Class HasNaturals `(C : Cat) :=
  { hasTerminal :: HasTerminal C
  ; Nat : Ob
  ; zero : Hom 1 Nat
  ; succ : Hom Nat Nat
  ; nat_rec {X} : Hom 1 X → Hom X X → Hom Nat X

  ; axiom_nat_rec_proper {X}
    :: Proper (@HomEq[1, X] ==> @HomEq[X, X] ==> @HomEq[Nat, X]) nat_rec

  ; axiom_naturals {X}
    : ∀ z : Hom 1 X, ∀ s : Hom X X,
        is_unique (λ f, f ∘ zero ≈ z ∧ f ∘ succ ≈ s ∘ f)
          (nat_rec z s)
  }.
