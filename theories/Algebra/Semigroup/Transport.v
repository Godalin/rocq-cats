From Cats Require Export
  Algebra.Semigroup.Core.
From Cats Require Export
  Algebra.Magma.Transport.

Local Open Scope algebra_scope.

(** * Transporting Associativity

    Associativity transfers to the exact magma from
    %\coqref{Cats.Algebra.Magma.Transport.MagmaTransport}
    {%[MagmaTransport]%}%. The one-sided
    recovery equation [f (g a) ≈S a] suffices: nested target products insert
    only this composite inside the source multiplication. *)

(** * 运输结合律

    将结合律运输到 %\coqref{Cats.Algebra.Magma.Transport.MagmaTransport}
    {%[MagmaTransport]%}%
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
  := let M := MagmaTransport A f g in
     SemigroupOfMagma M
       {|mul_assoc := _|}.
Next Obligation.
  change (g (f (g (f x ⋅ f y)) ⋅ f z) ≈S
    g (f x ⋅ f (g (f y ⋅ f z)))).
  apply (@func_proper _ _ g).
  transitivity ((f x ⋅ f y) ⋅ f z).
  - apply mul_proper; [apply Hfg | reflexivity].
  - transitivity (f x ⋅ (f y ⋅ f z)).
    + apply mul_assoc.
    + apply mul_proper; [reflexivity | symmetry; apply Hfg].
Defined.

End Transport.
