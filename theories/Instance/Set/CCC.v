From Cats Require Import Cat.CCC.
From Cats Require Import Instance.Set.Core Instance.Set.Terminal.
From Cats Require Import Instance.Set.Product Instance.Set.Exponential.

(** * The Cartesian Closed Category of Setoids *)

Definition SetCat_CCC : CCC :=
  {| C := SetCat
   ; hasTerminal := SetCat_HasTerminal
   ; hasProduct := SetCat_HasProduct
   ; hasExponential := SetCat_HasExponential |}.
