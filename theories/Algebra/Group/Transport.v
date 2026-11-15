From Cats Require Export
  Algebra.Group.Core.
From Cats Require Export
  Algebra.Monoid.Transport.

Local Open Scope monoid_scope.

(** * Transporting a Group

    Return the source inverse through [g], retaining the exact transported
    monoid. Inverse respectfulness, uniqueness and coherence then follow
    from the existing general group theory; no additional fields or laws
    are copied into a parallel interface. *)

(** * 运输群

    用 [g] 返回来源逆元，原样保留运输后的幺半群。逆的保相等性、唯一性及
    相干性继而由既有通用群理论导出；不将额外字段或定律复制进替代接口。 *)

(** ** A Supplied Group and Two Recovery Equations

    The maps preserve independently sized specified equalities. Choosing
    this group is explicit; importing the module selects no target algebra. *)

(** ** 给定群与双侧恢复方程

    映射保持大小独立的指定相等。群结构须显式选取；导入模块不选择目标代数。 *)

Section Transport.
Universe a r b s.
Context {A : SetC@{a r}} {B : SetC@{b s}}.
Context (f : B →r A) (g : A →r B).

(** Multiplication and unit are definitionally those of
    {{ coqref: Cats.Algebra.Monoid.Transport.MonoidTransport }}. The selected
    inverse computes as [g ((f x)⁻¹)]. *)

(** 乘法与单位元按定义就是
    {{ coqref: Cats.Algebra.Monoid.Transport.MonoidTransport }} 中的选择，
    选定逆计算为 [g ((f x)⁻¹)]。 *)

Program Definition GroupTransport (HA : Group A)
    (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp)
  : Group B
  :=
  {|GroupM := MonoidTransport f g HA Hfg Hgf
  ; group_inv x := g (@group_inv A HA (f x))
  |}.
Next Obligation.
  change (g (@magma_mul A HA
    (f (g (@group_inv A HA (f x)))) (f x)) ≈S g (@monoid_unit A HA)).
  apply (@func_proper _ _ g).
  transitivity (@magma_mul A HA (@group_inv A HA (f x)) (f x)).
  - apply (@magma_mul_proper A HA); [apply Hfg | reflexivity].
  - exact (@group_inv_l A HA (f x)).
Defined.
Next Obligation.
  change (g (@magma_mul A HA
    (f x) (f (g (@group_inv A HA (f x))))) ≈S g (@monoid_unit A HA)).
  apply (@func_proper _ _ g).
  transitivity (@magma_mul A HA (f x) (@group_inv A HA (f x))).
  - apply (@magma_mul_proper A HA); [reflexivity | apply Hfg].
  - exact (@group_inv_r A HA (f x)).
Defined.

(** The forward map preserves the selected inverse, in addition to the
    product and unit equations from the preceding transport layers. *)

(** 除前面运输层的乘积及单位方程外，正向映射还保持选定逆。 *)

Lemma group_transport_map_inv (HA : Group A)
    (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp) (x : B)
  : f (@group_inv B (GroupTransport HA Hfg Hgf) x) ≈S
      @group_inv A HA (f x).
Proof. exact (Hfg (@group_inv A HA (f x))). Defined.

End Transport.
