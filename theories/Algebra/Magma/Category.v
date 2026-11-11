From Cats Require Export
  Algebra.Magma.Core.
From Cats Require Import
  Cat.Core.

(** * Endomorphism Magmas *)

(** * 自态射原群 *)

(** Composition is a respectful binary operation on endomorphisms.
    This first layer uses neither associativity nor identity arrows. *)

(** 复合是自态射上的保相等二元运算。此第一层不使用结合律或恒等箭头。 *)

Program Definition EndMagma (C : Cat) (X : @Ob C)
  : Magma (HomSet X X)
  :=
  {|magma_mul g f := g ∘ f
  ; magma_mul_proper := comp_proper
  |}.
