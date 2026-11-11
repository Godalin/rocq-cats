From Cats Require Import
  Algebra.Magma.Core
  Instance.Set.Product.

Local Open Scope magma_scope.

(** * Magma Multiplication on a Product Set *)

(** * 乘积广集上的原群乘法 *)

(** A magma's multiplication gives a respectful map from the product set.
    This construction needs neither associativity nor a unit; internal
    monoid objects reuse it through their inherited magma. *)

(** 原群乘法给出从乘积广集出发的保相等映射。此构造无须结合律或单位元；
    内部幺半群对象通过继承的原群复用它。 *)

Program Definition set_magma_mul_resp {M : SetC} (HM : Magma M)
  : M ×S M →r M
  :=
  {|func p := fst p ⋅ snd p
  |}.
Next Obligation.
  intros [x y] [x' y'] [Hx Hy].
  exact (@magma_mul_proper M HM x x' Hx y y' Hy).
Defined.
