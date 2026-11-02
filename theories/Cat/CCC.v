From Stdlib Require Import Utf8.
From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product
  Cat.Exponential.
Open Scope cat_scope.



(** * Cartesian Closed Category *)

(** * 笛卡尔闭范畴 *)

(** A category equipped with a terminal object, binary products and
    exponentials. *)

(** 带有终对象、二元积和指数对象的范畴。 *)

Class CCC (C : Cat)
  :=
  { hasTerminal :: HasTerminal C
  ; hasProduct :: HasProduct C
  ; hasExponential :: HasExponential hasProduct
  }.

Section CCC.
Context {C : Cat} `{HCCC : !CCC C}.

(** The product of the terminal object with an object is isomorphic to that
    object. *)

(** 终对象与任意对象的积同构于该对象。 *)

Example idl {X}
  : 1 × X ≅ X.
Proof. apply term_prod_id_l. Qed.

End CCC.
