From Stdlib Require Import Utf8.
From Cats Require Import Meta.
From Cats Require Import Cat.Core.
From Cats Require Import ETCS.Nat.

Class ETCS U :=
  { C :: Cat U
  ; hasTerminal :: HasTerminal C
  ; hasProduct :: HasProduct C
  ; hasExponential :: HasExponential hasProduct
  ; hasNaturals :: HasNaturals C
  }.



Section ETCS.
Context {U} `{ETCS U}.

Check π1 ∘ (id × ƛ id).

End ETCS.
