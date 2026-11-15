From Cats Require Export
  Algebra.Monoid.Core.
From Cats Require Export
  Algebra.Semigroup.Transport.

Local Open Scope monoid_scope.

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
Universe a r b s.
Context {A : SetC@{a r}} {B : SetC@{b s}}.
Context (f : B →r A) (g : A →r B).

(** Retain the immediate semigroup parent, with unit explicitly computed
    from the supplied source monoid. *)

(** 保留直接半群父结构，单位元由给定来源幺半群显式计算。 *)

Program Definition MonoidTransport (HA : Monoid A)
    (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp)
  : Monoid B
  :=
  {|MonoidSG := SemigroupTransport f g HA Hfg
  ; monoid_unit := g (@monoid_unit A HA)
  |}.
Next Obligation.
  change (g (@magma_mul A HA (f (g (@monoid_unit A HA))) (f x)) ≈S x).
  transitivity (g (f x)); [apply (@func_proper _ _ g) | apply Hgf].
  transitivity (@magma_mul A HA (@monoid_unit A HA) (f x)).
  - apply (@magma_mul_proper A HA); [apply Hfg | reflexivity].
  - exact (@monoid_unit_l A HA (f x)).
Defined.
Next Obligation.
  change (g (@magma_mul A HA (f x) (f (g (@monoid_unit A HA)))) ≈S x).
  transitivity (g (f x)); [apply (@func_proper _ _ g) | apply Hgf].
  transitivity (@magma_mul A HA (f x) (@monoid_unit A HA)).
  - apply (@magma_mul_proper A HA); [reflexivity | apply Hfg].
  - exact (@monoid_unit_r A HA (f x)).
Defined.

(** The forward map preserves this same selected unit. *)

(** 正向映射保持这个同一选定单位元。 *)

Lemma monoid_transport_map_unit (HA : Monoid A)
    (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp)
  : f (@monoid_unit B (MonoidTransport HA Hfg Hgf)) ≈S
      @monoid_unit A HA.
Proof. exact (Hfg (@monoid_unit A HA)). Defined.

End Transport.
