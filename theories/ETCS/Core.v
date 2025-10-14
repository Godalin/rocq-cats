From Cats Require Import Cat.Core.
From Cats Require Import ETCS.Nat.

Class ETCS (C : Cat) :=
  { hasTerminal :: HasTerminal C
  ; hasProduct :: HasProduct C
  ; hasExponential :: HasExponential hasProduct
  ; hasNaturals :: HasNaturals C
  }.



Section ETCS.
Context {C : Cat} `{!ETCS C}.

Check π1 ∘ (id × ƛ id) × id.

End ETCS.
