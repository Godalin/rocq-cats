From Cats Require Export
  Algebra.Semigroup.Core.
From Cats Require Export
  Algebra.Magma.Transport.

Local Open Scope magma_scope.

(** * Transporting Associativity

    Associativity transfers to the exact magma from
    {{ coqref: Cats.Algebra.Magma.Transport.MagmaTransport }}. The one-sided
    recovery equation [f (g a) ≈S a] suffices: nested target products insert
    only this composite inside the source multiplication. *)

(** * 运输结合律

    将结合律运输到 {{ coqref: Cats.Algebra.Magma.Transport.MagmaTransport }}
    的同一原群。单侧恢复方程 [f (g a) ≈S a] 已足够：嵌套目标乘积只在来源
    乘法内部插入此复合。 *)

(** ** A Source Semigroup and One-Sided Recovery

    Keep both setoids and maps independent; require no unit, inverse or
    equation recovering elements of [B]. *)

(** ** 来源半群与单侧恢复

    保持两广集及映射独立；不要求单位元、逆或恢复 [B] 元素的方程。 *)

Section Transport.
Context (A : Semigroup) {B : SetC}.
Context (f : B →r A) (g : A →r B).

(** The unique immediate parent is the previously transported magma,
    with its multiplication unchanged. *)

(** 唯一直接父结构就是先前运输的原群，乘法原样保留。 *)

Program Definition SemigroupTransport (Hfg : (f ∘r g) ≈f id_resp)
  : Semigroup
  :=
  {|SemigroupM := MagmaTransport A f g
  ; isSemigroup := {|semigroup_assoc := _|}
  |}.
Next Obligation.
  change (g (@magma_mul _ (hasMagma A)
      (f (g (@magma_mul _ (hasMagma A) (f x) (f y)))) (f z)) ≈S
    g (@magma_mul _ (hasMagma A) (f x)
      (f (g (@magma_mul _ (hasMagma A) (f y) (f z)))))).
  apply (@func_proper _ _ g).
  transitivity (@magma_mul _ (hasMagma A)
    (@magma_mul _ (hasMagma A) (f x) (f y)) (f z)).
  - apply (@magma_mul_proper _ (hasMagma A)); [apply Hfg | reflexivity].
  - transitivity (@magma_mul _ (hasMagma A)
      (f x) (@magma_mul _ (hasMagma A) (f y) (f z))).
    + exact (@semigroup_assoc _ (isSemigroup A) (f x) (f y) (f z)).
    + apply (@magma_mul_proper _ (hasMagma A)); [reflexivity | symmetry; apply Hfg].
Defined.

End Transport.
