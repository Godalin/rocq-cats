From Cats Require Export
  Algebra.Group.Core
  Algebra.Monoid.Commutative.

Local Open Scope algebra_scope.

(** * Abelian Groups

    The group and the commutative monoid share their multiplication,
    associativity witness and unit. *)

(** * 阿贝尔群

    群和交换幺半群共享乘法、结合律见证及单位元。 *)

Minks.Struct AbGroup
  extends Group, CommMonoid.

(** Inversion preserves products in their original order when the group
    multiplication commutes. *)

(** 群乘法满足交换律时，取逆按原有次序保持乘积。 *)

Lemma inv_mul_comm {G : Group} `{HC : !IsCommMagma G} (x y : G)
  : (x ⋅ y)⁻¹ ≈S x⁻¹ ⋅ y⁻¹.
Proof.
  rewrite inv_mul. apply mul_comm.
Qed.
