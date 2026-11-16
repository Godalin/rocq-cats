From Cats Require Export
  Algebra.Magma.Core.

Local Open Scope magma_scope.

(** * Semigroups on Sets

    A semigroup adds associativity to one selected magma. Its operation
    and equality are inherited unchanged; no unit is required. *)

(** * 广集上的半群

    半群为一个选定原群增加结合律，原样继承其运算与相等，不要求单位元。 *)

(** Associativity is a property of one specified magma. It selects no
    additional operation, so no separate choice wrapper is needed. *)

(** 结合律是一个指定原群的性质，不选取额外运算，因而无须另加选择包装。 *)

Class IsSemigroup (M : Magma)
  :=
  { mul_assoc (x y z : M) : (x ⋅ y) ⋅ z ≈S x ⋅ (y ⋅ z)
  }.

(** The complete semigroup stores its immediate parent exactly once. *)

(** 完整半群恰好保存一次直接父结构。 *)

Record Semigroup@{u p l}
  :=
  { SemigroupToMagma :> Magma@{u p l}
  ; isSemigroup :: IsSemigroup SemigroupToMagma
  }.

(** Reuse an explicitly supplied parent and associativity witness. *)

(** 复用显式给定的父结构及结合律见证。 *)

Program Definition SemigroupFromProperty (M : Magma) (HM : IsSemigroup M)
  : Semigroup
  :=
  {|SemigroupToMagma := M
  ; isSemigroup := HM
  |}.

(** ** Associative Multiplication

    Fix a setoid with its selected semigroup structure; derive equations for
    repeated multiplication from its associative operation. *)

(** ** 结合乘法

    固定广集及其选定半群结构，从结合运算导出重复乘法的方程。 *)

Section Multiplication.
Context {S : Semigroup}.

(** Left multiplication sends a product to composition of respectful maps.
    This is the unit-free part of the left regular action. *)

(** 左乘将乘积送到保相等映射的复合，这是左正则作用中不依赖单位元的部分。 *)

Lemma mul_l_comp (x y : S)
  : ((x ⋅ y) ⋅−) ≈f ((x ⋅−) ∘r (y ⋅−)).
Proof. intros z. apply (@mul_assoc _ (isSemigroup S)). Qed.

(** Right multiplication reverses the order in the corresponding
    composition law. *)

(** 右乘在相应复合律中反转次序。 *)

Lemma mul_r_comp (x y : S)
  : (−⋅ (x ⋅ y)) ≈f ((−⋅ y) ∘r (−⋅ x)).
Proof. intros z. symmetry. apply (@mul_assoc _ (isSemigroup S)). Qed.

(** Left and right multiplication commute as maps, without requiring a
    commutative multiplication operation. *)

(** 左乘与右乘作为映射交换，无须乘法运算本身满足交换律。 *)

Lemma mul_lr_comm (x y : S)
  : ((x ⋅−) ∘r (−⋅ y)) ≈f ((−⋅ y) ∘r (x ⋅−)).
Proof. intros z. symmetry. apply (@mul_assoc _ (isSemigroup S)). Qed.

End Multiplication.
