From Cats Require Export
  Algebra.Semigroup.Core
  Algebra.Magma.Category.
From Cats Require Import
  Cat.Core.

(** * Endomorphism Semigroups

    Composition yields a semigroup before using the category's identity
    arrows. The monoid construction extends this same chosen parent. *)

(** * 自态射半群

    在使用范畴恒等箭头之前，复合已经给出半群；幺半群构造扩展同一个选定
    父结构。 *)

(** Associativity of category composition extends the same magma. *)

(** 范畴复合的结合律扩展同一个原群。 *)

Program Definition EndSemigroup (C : Cat) (X : @Ob C)
  : Semigroup (HomSet X X)
  :=
  {|SemigroupM := EndMagma C X
  ; semigroup_assoc := comp_assoc
  |}.
