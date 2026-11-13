From Cats Require Export
  Instance.Set.Arrow.
From Cats Require Import
  Cat.Computational.Arrow.StaticCartesian
  Cat.Exponential.Laws
  Cat.Isomorphism
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Exponential.
From Cats.Set Require Import
  Constant.

Local Open Scope computation_scope.
Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.

(** * Recovering an Applicative from Its Static Arrow

    Fix an Applicative on the existing closed setoid model, whose ambient
    carrier and equality share one level. Recover its values through the
    static Arrow, then compare the functors by a transparent natural
    isomorphism preserving pure values and ordered binary operations in
    both directions. This does not reconstruct arbitrary dynamic Arrows. *)

(** * 从静态 Arrow 回收 Applicative

    固定已有闭广集模型上的 Applicative，其所在载体与相等使用同一层级。
    经静态 Arrow 回收值，再以透明自然同构比较两个函子；双向保持纯值与
    有序二元运算。这里不重建任意动态 Arrow。 *)

Section Recovery.
Universe u.
Let C
  : Cat
  := SetCat@{u u _ _ _ _ _}.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasExponential.
Context (B : Applicative C SetCat_HasTerminal SetCat_HasProduct).

(** Recover Applicative values from the static Arrow of the original
    Applicative, with all model choices explicit. *)

(** 从原 Applicative 的静态 Arrow 回收 Applicative 值，全部模型选择显式给出。 *)

Definition StaticRecoveredA
  : Applicative C SetCat_HasTerminal SetCat_HasProduct
  := ArrowA (StaticCat B) (StaticArrow B).

(** First evaluate the outer global element, then map terminal-argument
    evaluation through the original Applicative. Both stages reuse the
    selected exponential-unit isomorphism and retain explicit inverses. *)

(** 先求值外层全局元素，再通过原 Applicative 映射终参数求值。两步均复用
    选定指数单位同构，并保留显式逆。 *)

Definition StaticRecoveryIso (X : @Ob C)
  : StaticRecoveredA X ≅[C] B X
  := iso_trans (exponential_unit_iso (B (X ^ 1)%ob))
    (fmap B (exponential_unit_iso X).1;
      functor_is_iso B (exponential_unit_iso X).1 (exponential_unit_iso X).2).

(** The recovery maps are natural by the existing static result-map law. *)

(** 回收映射的自然性来自已有静态结果映射定律。 *)

Program Definition StaticRecoveryN
  : StaticRecoveredA ⇒ B
  :=
  {|nt X := (StaticRecoveryIso X).1
  |}.
Next Obligation.
  intros h.
  change (static_value B (static_arr B f ∘ˢ[B] h) tt ≈S
    fmap B f (static_value B h tt)).
  exact (static_value_map B f h tt).
Defined.

(** The recovered and original functors are naturally isomorphic,
    without equality of functor or law records. *)

(** 回收与原函子自然同构，不要求函子或定律记录相等。 *)

Definition StaticRecoveryNatIso
  : StaticRecoveredA ≅N B
  := (StaticRecoveryN; λ X, (StaticRecoveryIso X).2).

(** Recovery preserves pure values pointwise in the original setoid equality. *)

(** 回收在原有广集相等下逐点保持纯值。 *)

Lemma static_recovery_pure (X : @Ob C)
  : (StaticRecoveryN X) ∘ pure[StaticRecoveredA] X ≈ pure[B] X.
Proof.
  intros x.
  change (static_value B (static_arr B (const_resp UnitS x)) tt ≈S pure[B] X x).
  exact (static_value_pure B (const_resp UnitS x) tt).
Qed.

(** Recovery preserves the original ordered Applicative tensorator.
    Apply the functor identity law directly to the computed value, keeping
    the effectful computation opaque to rewriting. *)

(** 回收保持原有有序 Applicative tensorator；将函子恒等律直接应用于所得值，
    避免重写展开带效应计算。 *)

Lemma static_recovery_pair (X Y : @Ob C)
  : StaticRecoveryN (X × Y)%ob ∘ φ₂[StaticRecoveredA; X; Y] ≈
      φ₂[B; X; Y] ∘ (StaticRecoveryN X × StaticRecoveryN Y).
Proof.
  intros [f g].
  etransitivity; [exact (static_value_fanout B f g tt) |].
  exact (@functor_id C C B (X × Y)%ob
    (φ₂[B; X; Y] (static_value B f tt, static_value B g tt))).

Qed.

(** Recovery preserves every lifted ordinary binary operation. *)

(** 回收保持每个提升后的通常二元运算。 *)

Lemma static_recovery_lift2 {X Y Z : @Ob C} (h : X ×S Y →r Z)
  : StaticRecoveryN Z ∘ lift₂[StaticRecoveredA; h] ≈
      lift₂[B; h] ∘ (StaticRecoveryN X × StaticRecoveryN Y).
Proof.
  intros [f g].
  change (static_value B
    (static_arr B h ∘ˢ[B] (f &&&[StaticArrow B] g)) tt ≈S
    lift₂[B; h] (static_value B f tt, static_value B g tt)).
  exact (static_value_fanout_map B h f g tt).
Qed.

(** The inverse transformation reuses the general natural-isomorphism
    inversion theorem and the same chosen inverse components. *)

(** 逆变换复用一般自然同构求逆定理及同一组选定逆分量。 *)

Definition StaticRecoveryInvN
  : B ⇒ StaticRecoveredA
  := NatIso_inv StaticRecoveryN (λ X, (StaticRecoveryIso X).2).

(** Abstract left round trip, so clients need not reduce the chosen
    inverse witness on a large computation. *)

(** 抽象的左往返定律，使客户端无需在大计算上归约选定逆见证。 *)

Lemma static_recovery_inv_l (X : @Ob C) (v : StaticRecoveredA X)
  : StaticRecoveryInvN X (StaticRecoveryN X v) ≈S v.
Proof. exact (fst (StaticRecoveryIso X).2.2 v). Qed.

(** The forward map also cancels the inverse on every original value. *)

(** 对每个原有值，正向映射也消去逆映射。 *)

Lemma static_recovery_inv_r (X : @Ob C) (v : B X)
  : StaticRecoveryN X (StaticRecoveryInvN X v) ≈S v.
Proof. exact (snd (StaticRecoveryIso X).2.2 v). Qed.

(** The inverse transformation also preserves pure values. *)

(** 逆变换也保持纯值。 *)

Lemma static_recovery_inverse_pure (X : @Ob C)
  : StaticRecoveryInvN X ∘ pure[B] X ≈ pure[StaticRecoveredA] X.
Proof.
  intros x.
  transitivity (StaticRecoveryInvN X
    (StaticRecoveryN X (pure[StaticRecoveredA] X x))).
  - apply (@func_proper _ _ (StaticRecoveryInvN X)).
    symmetry. exact (static_recovery_pure X x).
  - exact (static_recovery_inv_l X (pure[StaticRecoveredA] X x)).
Qed.

(** The inverse transformation preserves ordered pairing, using only
    the forward comparison, respectfulness and the two inverse equations. *)

(** 逆变换保持有序配对，只使用正向比较、尊重性及两条互逆方程。 *)

Lemma static_recovery_inverse_pair (X Y : @Ob C)
  : StaticRecoveryInvN (X × Y)%ob ∘ φ₂[B; X; Y] ≈
      φ₂[StaticRecoveredA; X; Y] ∘
        (StaticRecoveryInvN X × StaticRecoveryInvN Y).
Proof.
  intros [f g].
  transitivity (StaticRecoveryInvN (X × Y)%ob
    (StaticRecoveryN (X × Y)%ob
      (φ₂[StaticRecoveredA; X; Y] (StaticRecoveryInvN X f,
        StaticRecoveryInvN Y g)))).
  - apply (@func_proper _ _ (StaticRecoveryInvN (X × Y)%ob)).
    symmetry. etransitivity.
    + exact (static_recovery_pair X Y
        (StaticRecoveryInvN X f, StaticRecoveryInvN Y g)).
    + apply (@func_proper _ _ φ₂[B; X; Y]). split;
        [exact (static_recovery_inv_r X f) |
         exact (static_recovery_inv_r Y g)].
  - exact (static_recovery_inv_l (X × Y)%ob
      (φ₂[StaticRecoveredA; X; Y] (StaticRecoveryInvN X f,
        StaticRecoveryInvN Y g))).
Qed.

(** The inverse also preserves every lifted ordinary binary operation. *)

(** 逆变换也保持每个提升后的通常二元运算。 *)

Lemma static_recovery_inverse_lift2 {X Y Z : @Ob C} (h : X ×S Y →r Z)
  : StaticRecoveryInvN Z ∘ lift₂[B; h] ≈
      lift₂[StaticRecoveredA; h] ∘
        (StaticRecoveryInvN X × StaticRecoveryInvN Y).
Proof.
  intros [f g].
  transitivity (StaticRecoveryInvN Z
    (StaticRecoveryN Z
      (lift₂[StaticRecoveredA; h] (StaticRecoveryInvN X f,
        StaticRecoveryInvN Y g)))).
  - apply (@func_proper _ _ (StaticRecoveryInvN Z)).
    symmetry. etransitivity.
    + exact (static_recovery_lift2 h
        (StaticRecoveryInvN X f, StaticRecoveryInvN Y g)).
    + apply (@func_proper _ _ lift₂[B; h]). split;
        [exact (static_recovery_inv_r X f) |
         exact (static_recovery_inv_r Y g)].
  - exact (static_recovery_inv_l Z
      (lift₂[StaticRecoveredA; h] (StaticRecoveryInvN X f,
        StaticRecoveryInvN Y g))).
Qed.

End Recovery.
