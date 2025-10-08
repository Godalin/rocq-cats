From Stdlib Require Import Utf8.
From Cats Require Import Cat.Core.
Open Scope cat_scope.


(* TODO exp objects *)

Class CCC (U : Type) :=
  { C :: Cat U
  ; hasTerminal :: HasTerminal C
  ; hasProduct :: HasProduct C
  }.



Section CCC.
Context {U} `{CCC U}.

Example idl {X} : 1 × X ≅ X.
Proof. apply term_prod_id_l. Qed.

End CCC.
