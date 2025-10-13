From Coq Require Import Utf8.
From Cats Require Import Meta.
From Cats Require Import Cat.Core.

Class HasNaturals `(C : Cat) :=
  { hasTerminal :: HasTerminal C
  ; Nat : Ob
  ; zero : Hom 1 Nat
  ; succ : Hom Nat Nat
  ; nat_rec {X} : Hom 1 X → Hom X X → Hom Nat X
  ; axiom_naturals {X}
    : ∀ z : Hom 1 X, ∀ s : Hom X X,
        is_unique (λ f, f ∘ zero = z ∧ f ∘ succ = s ∘ f)
          (nat_rec z s)
  }.
