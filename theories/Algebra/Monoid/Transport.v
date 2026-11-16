From Cats Require Export
  Algebra.Monoid.Core.
From Cats Require Export
  Algebra.Semigroup.Transport.

Local Open Scope algebra_scope.

(** * Transporting a Unit

    Add the returned source unit [g 1] to the same transported semigroup.
    Unlike associativity, the unit laws also need [g (f b) ≈S b]: after
    applying a source unit law one must recover the original target input. *)

(** * 运输单位元

    为同一运输半群添加返回的来源单位元 [g 1]。与结合律不同，单位律还需要
    [g (f b) ≈S b]：应用来源单位律后，必须恢复原来的目标输入。 *)

(** ** Pointwise Mutually Inverse Maps

    Fix both recovery equations in the specified equalities. Their witnesses
    need not be native equal, and the two carrier/equality sizes stay separate. *)

(** ** 逐点互逆映射

    在指定相等下固定双侧恢复方程，不要求见证的原生相等；两载体及相等大小
    仍然独立。 *)

Section Transport.
Context (A : Monoid) {B : SetC}.
Context (f : B →r A) (g : A →r B).

(** Retain the immediate semigroup parent, with unit explicitly computed
    from the supplied source monoid. *)

(** 保留直接半群父结构，单位元由给定来源幺半群显式计算。 *)

Program Definition HasMonoidTransport (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : HasMonoid (SemigroupTransport A f g Hfg)
  :=
  {|mul_unit := g 1
  ; isMonoid :=
      {|mul_unit_l := _
      ; mul_unit_r := _
      |}
  |}.
Next Obligation.
  change (g (f (g 1) ⋅ f x) ≈S x).
  transitivity (g (f x)); [apply (@func_proper _ _ g) | apply Hgf].
  transitivity (1 ⋅ f x).
  - apply mul_proper; [apply Hfg | reflexivity].
  - exact (mul_unit_l (f x)).
Defined.
Next Obligation.
  change (g (f x ⋅ f (g 1)) ≈S x).
  transitivity (g (f x)); [apply (@func_proper _ _ g) | apply Hgf].
  transitivity (f x ⋅ 1).
  - apply mul_proper; [reflexivity | apply Hfg].
  - exact (mul_unit_r (f x)).
Defined.

(** Pack the transported semigroup and its chosen unit extension. *)

(** 将运输半群及其选定单位扩充打包。 *)

Definition MonoidTransport
    (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : Monoid
  := MonoidOfSemigroup (SemigroupTransport A f g Hfg)
      (HasMonoidTransport Hfg Hgf).

(** The forward map preserves this same selected unit. *)

(** 正向映射保持这个同一选定单位元。 *)

Lemma monoid_transport_map_unit (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : f (1 : MonoidTransport Hfg Hgf) ≈S 1.
Proof. exact (Hfg 1). Defined.

End Transport.
