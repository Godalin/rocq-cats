From Stdlib Require Import Utf8.
From Cats Require Import Cat.Core.
Open Scope cat_scope.


(* TODO exp objects *)

Class CCC (Ob : Type) :=
  { C :: Cat Ob
  ; hasTerminal :: HasTerminal C
  ; hasProduct :: HasProduct C
  }.



Section CCC.
Context {Ob} `{CCC Ob}.

Example x {X} : 1 × X ≅ X.
Proof. apply term_prod_id_l. Qed.

End CCC.
