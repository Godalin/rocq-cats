From Cats Require Export
  Algebra.Group.Core.
From Cats Require Export
  Algebra.Monoid.Transport.

Local Open Scope algebra_scope.

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
Context (A : Group) {B : SetC}.
Context (f : B →r A) (g : A →r B).

(** Multiplication and unit are definitionally those of
    {{ coqref: Cats.Algebra.Monoid.Transport.MonoidTransport }}. The selected
    inverse computes as [g ((f x)⁻¹)]. *)

(** 乘法与单位元按定义就是
    {{ coqref: Cats.Algebra.Monoid.Transport.MonoidTransport }} 中的选择，
    选定逆计算为 [g ((f x)⁻¹)]。 *)

Program Definition HasGroupTransport
    (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : HasGroup (MonoidTransport A f g Hfg Hgf)
  :=
  {|inv x := g ((f x)⁻¹)
  ; isGroup :=
      {|mul_inv_l := _
      ; mul_inv_r := _
      |}
  |}.
Next Obligation.
  change (g (f (g ((f x)⁻¹)) ⋅ f x) ≈S g 1).
  apply (@func_proper _ _ g).
  transitivity ((f x)⁻¹ ⋅ f x).
  - apply mul_proper; [apply Hfg | reflexivity].
  - exact (mul_inv_l (f x)).
Defined.
Next Obligation.
  change (g (f x ⋅ f (g ((f x)⁻¹))) ≈S g 1).
  apply (@func_proper _ _ g).
  transitivity (f x ⋅ (f x)⁻¹).
  - apply mul_proper; [reflexivity | apply Hfg].
  - exact (mul_inv_r (f x)).
Defined.

(** Recover the existing group presentation from the exact transported
    monoid and its chosen inverse extension. *)

(** 从恰好同一运输幺半群及其选定逆扩充恢复现有群呈现。 *)

Definition GroupTransport
    (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : Group
  := GroupOfMonoid (MonoidTransport A f g Hfg Hgf)
      (HasGroupTransport Hfg Hgf).

(** The forward map preserves the selected inverse, in addition to the
    product and unit equations from the preceding transport layers. *)

(** 除前面运输层的乘积及单位方程外，正向映射还保持选定逆。 *)

Lemma group_transport_map_inv
    (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
    (x : B)
  : f ((x : GroupTransport Hfg Hgf)⁻¹) ≈S (f x)⁻¹.
Proof. exact (Hfg ((f x)⁻¹)). Defined.

End Transport.
