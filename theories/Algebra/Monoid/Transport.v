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
Context (A : Monoid) {B : SetC}.
Context (f : B →r A) (g : A →r B).

(** Retain the immediate semigroup parent, with unit explicitly computed
    from the supplied source monoid. *)

(** 保留直接半群父结构，单位元由给定来源幺半群显式计算。 *)

Program Definition HasMonoidTransport (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : HasMonoid (SemigroupTransport A f g Hfg)
  :=
  {|monoid_unit := g (@monoid_unit _ (hasMonoid A))
  ; isMonoid :=
      {|mul_unit_l := _
      ; mul_unit_r := _
      |}
  |}.
Next Obligation.
  change (g (@mul _ (hasMagma A) (f (g (@monoid_unit _ (hasMonoid A)))) (f x)) ≈S x).
  transitivity (g (f x)); [apply (@func_proper _ _ g) | apply Hgf].
  transitivity (@mul _ (hasMagma A) (@monoid_unit _ (hasMonoid A)) (f x)).
  - apply (@mul_proper _ (hasMagma A)); [apply Hfg | reflexivity].
  - exact (@mul_unit_l _ _ (@isMonoid _ (hasMonoid A)) (f x)).
Defined.
Next Obligation.
  change (g (@mul _ (hasMagma A) (f x) (f (g (@monoid_unit _ (hasMonoid A))))) ≈S x).
  transitivity (g (f x)); [apply (@func_proper _ _ g) | apply Hgf].
  transitivity (@mul _ (hasMagma A) (f x) (@monoid_unit _ (hasMonoid A))).
  - apply (@mul_proper _ (hasMagma A)); [reflexivity | apply Hfg].
  - exact (@mul_unit_r _ _ (@isMonoid _ (hasMonoid A)) (f x)).
Defined.

(** Pack the transported semigroup and its chosen unit extension. *)

(** 将运输半群及其选定单位扩充打包。 *)

Definition MonoidTransport
    (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : Monoid
  := MonoidFromExtension (SemigroupTransport A f g Hfg)
      (HasMonoidTransport Hfg Hgf).

(** The forward map preserves this same selected unit. *)

(** 正向映射保持这个同一选定单位元。 *)

Lemma monoid_transport_map_unit (Hfg : (f ∘r g) ≈f id_resp)
    (Hgf : (g ∘r f) ≈f id_resp)
  : f (@monoid_unit _ (hasMonoid (MonoidTransport Hfg Hgf))) ≈S
      @monoid_unit _ (hasMonoid A).
Proof. exact (Hfg (@monoid_unit _ (hasMonoid A))). Defined.

End Transport.
