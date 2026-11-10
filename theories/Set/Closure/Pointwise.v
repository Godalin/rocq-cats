From Cats.Set.Closure Require Export Core.

(** * Pointwise Families of Closures

    A supplied closure in every fiber acts on dependent functions
    pointwise. This needs no equality or transport between indices and
    no choice principle: all the component operations are already data. *)

(** * 闭包的逐点族

    每个纤维中给定的闭包逐点作用于依赖函数。不需要索引之间的相等、运输或
    选择原理：全部分量操作都已经作为数据给出。 *)

(** Lift component closure laws without comparing dependent functions by
    native equality. The order is the pointwise family of supplied orders. *)

(** 提升分量闭包律，不按原生相等比较依赖函数；顺序使用所给顺序的逐点族。 *)

Program Definition PointwiseClosure {I : Type} {X : I → Type}
    (R : ∀ i, crelation (X i)) (c : ∀ i, Closure (R i))
  : Closure (λ x y : ∀ i, X i, ∀ i, R i (x i) (y i))
  :=
  {|closure_map x i := c i (x i)
  |}.
Next Obligation.
  split.
  - intros x y h i. exact (closure_monotone (c i) (h i)).
  - split.
    + intros x i. exact (closure_inflate (c i) (x i)).
    + intros x i. exact (closure_flatten (c i) (x i)).
Defined.
