From Coq Require Import Utf8.
From Cats Require Import Cat.Core.
Open Scope cat_scope.


(* TODO exp objects *)

Class CCC :=
  { C :: Cat
  ; hasTerminal :: HasTerminal C
  ; hasProduct :: HasProduct C
  ; hasExponential :: HasExponential hasProduct
  }.



Section CCC.
Context `{CCC}.

Example idl {X} : 1 × X ≅ X.
Proof. apply term_prod_id_l. Qed.

End CCC.
