From Cats Require Export
  Algebra.Monoid.Core.

Local Open Scope monoid_scope.

(** * Commutative Coefficients

    A monoid need not allow its factors to be exchanged. Record that extra
    law for the already selected multiplication, in its specified equality.
    A group with this property is an abelian group; no second monoid or
    group structure is selected here.

    When triangle labels are combined, the middle factors in a product of
    four coefficients must sometimes exchange places. The interchange law
    below isolates precisely that use of commutativity. It needs no inverses. *)

(** * 交换系数

    幺半群不一定允许交换因子。这里为已经选定的乘法记录这一额外定律，使用
    其指定相等。具有此性质的群就是交换群；这里不另选第二套幺半群或群结构。

    合并三角形标签时，有时需要交换四个系数中间两个的位置。下方的交换定律
    单独刻画这一步所需的交换性，不要求存在逆。 *)

Class IsCommutativeMonoid (M : SetC) `{HM : !Monoid M}
  :=
  { monoid_mul_comm (x y : M)
    : x ⋅ y ≈S y ⋅ x
  }.

(** ** Exchanging the Middle Factors

    Fix the selected monoid [M] and a commutativity witness. Associativity
    changes the brackets; commutativity exchanges only the middle pair. *)

(** ** 交换中间两个因子

    固定选定幺半群 [M] 及其交换性见证。结合律改变括号，交换律只交换中间
    的一对因子。 *)

Section Interchange.
Context {M : SetC} `{HM : !Monoid M} `{HC : !IsCommutativeMonoid M}.

(** Multiplying two pairs can be regrouped by their first and second entries. *)

(** 两对元素的乘积可以按各自的第一、第二分量重新分组。 *)

Lemma monoid_mul_interchange (a b c d : M)
  : (a ⋅ b) ⋅ (c ⋅ d) ≈S (a ⋅ c) ⋅ (b ⋅ d).
Proof.
  rewrite semigroup_assoc, <- (semigroup_assoc b c d), (monoid_mul_comm b c),
    (semigroup_assoc c b d), <- semigroup_assoc.
  reflexivity.
Defined.

End Interchange.
