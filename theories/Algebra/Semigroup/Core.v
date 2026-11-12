From Cats Require Export
  Algebra.Magma.Core.

Local Open Scope magma_scope.

(** * Semigroups on Sets

    A semigroup adds associativity to one selected magma. Its operation
    and equality are inherited unchanged; no unit is required. *)

(** * 广集上的半群

    半群为一个选定原群增加结合律，原样继承其运算与相等，不要求单位元。 *)

Class Semigroup (S : SetC)
  :=
  (** The magma is the unique immediate parent. *)

  (** 原群是唯一直接父结构。 *)

  { SemigroupM :> Magma S

  (** Associativity uses the inherited multiplication and equality. *)

  (** 结合律使用继承的乘法及相等。 *)

  ; semigroup_assoc x y z : (x ⋅ y) ⋅ z ≈S x ⋅ (y ⋅ z)
  }.

Arguments SemigroupM {_} _.

(** Make that same parent available to instance search. *)

(** 将同一父结构提供给实例搜索。 *)

#[export] Existing Instance SemigroupM.

(** ** Associative Multiplication

    Fix a setoid with its selected semigroup structure; derive equations for
    repeated multiplication from its associative operation. *)

(** ** 结合乘法

    固定广集及其选定半群结构，从结合运算导出重复乘法的方程。 *)

Section Multiplication.
Context {S : SetC} `{HS : !Semigroup S}.

(** Left multiplication sends a product to composition of respectful maps.
    This is the unit-free part of the left regular action. *)

(** 左乘将乘积送到保相等映射的复合，这是左正则作用中不依赖单位元的部分。 *)

Lemma semigroup_mul_l_comp (x y : S)
  : magma_mul_l_resp (x ⋅ y) ≈f
      (magma_mul_l_resp x ∘r magma_mul_l_resp y).
Proof. intros z. apply semigroup_assoc. Qed.

(** Right multiplication reverses the order in the corresponding
    composition law. *)

(** 右乘在相应复合律中反转次序。 *)

Lemma semigroup_mul_r_comp (x y : S)
  : magma_mul_r_resp (x ⋅ y) ≈f
      (magma_mul_r_resp y ∘r magma_mul_r_resp x).
Proof. intros z. symmetry. apply semigroup_assoc. Qed.

(** Left and right multiplication commute as maps, without requiring a
    commutative multiplication operation. *)

(** 左乘与右乘作为映射交换，无须乘法运算本身满足交换律。 *)

Lemma semigroup_mul_lr_comm (x y : S)
  : (magma_mul_l_resp x ∘r magma_mul_r_resp y) ≈f
      (magma_mul_r_resp y ∘r magma_mul_l_resp x).
Proof. intros z. symmetry. apply semigroup_assoc. Qed.

End Multiplication.
