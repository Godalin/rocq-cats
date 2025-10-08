From Stdlib Require Import Utf8.
From Cats Require Import Cat.Core.
From Cats Require Import ETCS.Nat.

Class ETCS U :=
  { C :: Cat U

  }.
