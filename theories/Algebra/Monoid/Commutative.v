From Cats Require Export
  Algebra.Monoid.Core.

Local Open Scope algebra_scope.

(** * Commutative Coefficients

    Commutativity compares products in the specified setoid equality of
    the chosen magma. Associativity then lets us exchange the middle
    factors in a product of four coefficients.

    The middle-factor law is used when combining triangle labels. *)

(** * 交换系数

    交换律使用选定原群的广集相等比较乘积，再借助结合律便可交换四个
    因子中的中间两项。合并三角形标签时会用到这一交换。 *)

Minks.Mixin IsCommMagma (S : SetC)
  extends HasMagma S
  :=
  { mul_comm (x y : S)
    : mul x y ≈S mul y x
  }.

Arguments mul_comm {_ _ _} x y.

(** A commutative monoid equips its own multiplication with commutativity. *)

(** 交换幺半群为其选定的乘法配备交换律。 *)

Minks.Struct CommMonoid
  extends Monoid
  with  isCommMagma : IsCommMagma.

(** ** Exchanging the Middle Factors

    Fix the selected semigroup [M] and a commutativity witness. Associativity
    changes the brackets; commutativity exchanges only the middle pair. *)

(** ** 交换中间两个因子

    固定选定半群 [M] 及其交换性见证。结合律改变括号，交换律只交换中间
    的一对因子。 *)

Section Interchange.
Context {M : Semigroup} `{HC : !IsCommMagma M}.

(** Multiplying two pairs can be regrouped by their first and second entries. *)

(** 两对元素的乘积可以按各自的第一、第二分量重新分组。 *)

Lemma mul_interchange (a b c d : M)
  : (a ⋅ b) ⋅ (c ⋅ d) ≈S (a ⋅ c) ⋅ (b ⋅ d).
Proof.
  rewrite mul_assoc, <- (mul_assoc b c d),
    (mul_comm b c), (mul_assoc c b d),
    <- (mul_assoc a c (b ⋅ d)).
  reflexivity.
Defined.

End Interchange.
