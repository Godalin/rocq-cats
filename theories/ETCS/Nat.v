From Stdlib Require Import Utf8.
From Cats Require Import Meta.
From Cats Require Import Cat.Core.

Class HasNNO {U} `(C : Cat U) :=
  { Nat : Ob
  ; nat_arr {X} : Hom Nat X
  ; axiom_natural_object
    : Type
  }.
