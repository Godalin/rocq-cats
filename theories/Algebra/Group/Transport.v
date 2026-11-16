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
Context (A : Group) {B : SetC}.
Context (f : B →r A) (g : A →r B).

(** Multiplication and unit are definitionally those of
    {{ coqref: Cats.Algebra.Monoid.Transport.MonoidTransport }}. The selected
    inverse computes as [g ((f x)⁻¹)]. *)

(** 乘法与单位元按定义就是
    {{ coqref: Cats.Algebra.Monoid.Transport.MonoidTransport }} 中的选择，
    选定逆计算为 [g ((f x)⁻¹)]。 *)

Program Definition HasGroupTransport (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : HasGroup (MonoidTransport A f g Hfg Hgf)
  :=
  {|inv x := g (@inv _ (hasGroup A) (f x))
  ; isGroup :=
      {|mul_inv_l := _
      ; mul_inv_r := _
      |}
  |}.
Next Obligation.
  change (g (@mul _ (hasMagma A)
    (f (g (@inv _ (hasGroup A) (f x)))) (f x)) ≈S g (@monoid_unit _ (hasMonoid A))).
  apply (@func_proper _ _ g).
  transitivity (@mul _ (hasMagma A) (@inv _ (hasGroup A) (f x)) (f x)).
  - apply (@mul_proper _ (hasMagma A)); [apply Hfg | reflexivity].
  - exact (@mul_inv_l _ _ (@isGroup _ (hasGroup A)) (f x)).
Defined.
Next Obligation.
  change (g (@mul _ (hasMagma A)
    (f x) (f (g (@inv _ (hasGroup A) (f x))))) ≈S g (@monoid_unit _ (hasMonoid A))).
  apply (@func_proper _ _ g).
  transitivity (@mul _ (hasMagma A) (f x) (@inv _ (hasGroup A) (f x))).
  - apply (@mul_proper _ (hasMagma A)); [reflexivity | apply Hfg].
  - exact (@mul_inv_r _ _ (@isGroup _ (hasGroup A)) (f x)).
Defined.

(** Recover the existing group presentation from the exact transported
    monoid and its chosen inverse extension. *)

(** 从恰好同一运输幺半群及其选定逆扩充恢复现有群呈现。 *)

Definition GroupTransport (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : Group
  := GroupFromExtension (MonoidTransport A f g Hfg Hgf)
      (HasGroupTransport Hfg Hgf).

(** The forward map preserves the selected inverse, in addition to the
    product and unit equations from the preceding transport layers. *)

(** 除前面运输层的乘积及单位方程外，正向映射还保持选定逆。 *)

Lemma group_transport_map_inv (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp) (x : B)
  : f (@inv _ (hasGroup (GroupTransport Hfg Hgf)) x) ≈S
      @inv _ (hasGroup A) (f x).
Proof. exact (Hfg (@inv _ (hasGroup A) (f x))). Defined.

End Transport.
