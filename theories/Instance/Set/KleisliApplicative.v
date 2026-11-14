From Cats Require Export
  Cat.Computational.Arrow.DynamicApplicative
  Instance.Set.KleisliRecovery.
From Cats Require Import
  Cat.Computational.Arrow.Applicative
  Instance.Set.Arrow
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope computation_scope.
Local Open Scope monad_scope.
Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * Direct and Kleisli-Derived Applicatives

    Fix a strong Monad on the existing native Kleisli recovery model, at
    its common carrier/equality bound. Keep its supplied strength. The
    evaluation/constant natural isomorphism already used for Monad recovery
    compares direct Monad Applicative values with the Kleisli Arrow's
    terminal-input computations. Both directions preserve the operations.
    The resulting comparison triangle commutes in natural-transformation
    equality; no equality of Applicative or strength records is needed. *)

(** * 直接与 Kleisli 导出的 Applicative

    固定已有原生 Kleisli 回收模型上的强 Monad，使用其共同载体／相等界，保留
    所给强度。Monad 回收中已有的求值／常值自然同构，将直接 Monad Applicative
    值与 Kleisli Arrow 的终输入计算比较。双向均保持运算。所得比较三角在自然
    变换相等下交换，不要求 Applicative 或强度记录相等。 *)

Section Comparison.
Universe u.
Context (M : StrongMonad (SetCat@{u u _ _ _ _ _}) SetCartesianMonoidal).

(** Reuse the Monad recovery components and their naturality. Repackage
    them on the actual global-computation functor; functor law records
    need not be definitionally equal. *)

(** 复用 Monad 回收分量及其自然性，将它们重新打包到实际全局计算函子上；
    不要求函子定律记录定义相等。 *)

Program Definition KleisliApplicativeN
  : ArrowA (KleisliCat M) (KleisliArrow M) ⇒ MonadA M
  :=
  {|nt X := KleisliRecoveryN M X
  |}.
Next Obligation. exact (nt_naturality (KleisliRecoveryN M) f). Defined.

(** Keep the exact evaluation/constant inverse components of Monad recovery. *)

(** 保留 Monad 回收中恰好相同的求值／常值逆分量。 *)

Definition KleisliApplicativeIso
  : ArrowA (KleisliCat M) (KleisliArrow M) ≅N MonadA M
  := (KleisliApplicativeN; (KleisliRecoveryNatIso M).2).

(** The chosen inverse is the original constant-computation map. Its
    naturality is inherited from the forward natural isomorphism. *)

(** 选定逆是原有常值计算映射，其自然性继承自正向自然同构。 *)

Definition KleisliApplicativeInvN
  : MonadA M ⇒ ArrowA (KleisliCat M) (KleisliArrow M)
  := KleisliApplicativeN ^-1N KleisliApplicativeIso.2.

(** Terminal-input evaluation preserves pure values and ordered pairing
    by the general Kleisli fanout law, using the original chosen strength. *)

(** 终输入求值由一般 Kleisli fanout 律保持纯值与有序配对，使用原选定强度。 *)

Lemma kleisli_applicative_hom
  : is_applicative_hom (ArrowA (KleisliCat M) (KleisliArrow M))
      (MonadA M) KleisliApplicativeN.
Proof.
  split.
  - intros X x. reflexivity.
  - intros X Y [f g].
    change (@arrow_fanout SetCat (KleisliCat M) SetCat_HasTerminal
      SetCat_HasProduct (KleisliArrow M) UnitS X Y f g tt ≈S
      @monad_pair SetCat SetCat_HasTerminal SetCat_HasProduct M X Y
        (f tt,g tt)).
    exact (@kleisli_arrow_fanout SetCat SetCat_HasTerminal
      SetCat_HasProduct M UnitS X Y f g tt).
Qed.

(** The existing constant-computation inverse preserves the operations
    by the general natural-isomorphism inverse theorem. *)

(** 已有常值计算逆由一般自然同构求逆定理保持运算。 *)

Lemma kleisli_applicative_inverse_hom
  : is_applicative_hom (MonadA M)
      (ArrowA (KleisliCat M) (KleisliArrow M)) KleisliApplicativeInvN.
Proof.
  exact (applicative_hom_inverse _ _ _ kleisli_applicative_hom
    (KleisliApplicativeIso.2)).
Qed.

(** The recovered Monad's identity comparison followed by terminal-input
    evaluation is the original Monad recovery transformation. *)

(** 回收 Monad 的恒等比较后接终输入求值，就是原有 Monad 回收自然变换。 *)

Lemma kleisli_applicative_triangle
  : (KleisliApplicativeIso.1 ∘Nv
      (DynamicApplicativeIso (KleisliArrowApply M)).1) ≈N
      (KleisliRecoveryNatIso M).1.
Proof. intros X m. reflexivity. Qed.

(** The inverse triangle uses the same constant-computation map. *)

(** 逆向三角使用同一个常值计算映射。 *)

Lemma kleisli_applicative_inverse_triangle
  : (((DynamicApplicativeIso (KleisliArrowApply M)).1 ^-1N
        (DynamicApplicativeIso (KleisliArrowApply M)).2) ∘Nv
      KleisliApplicativeInvN) ≈N KleisliRecoveryInvN M.
Proof. intros X m. reflexivity. Qed.

(** Recovering the Monad also preserves its derived Applicative. Compose
    the two comparisons rather than reproving contextual sequencing laws. *)

(** 回收 Monad 也保持其导出 Applicative；复合两个比较，无需重证上下文组合律。 *)

Lemma kleisli_recovered_applicative_hom
  : is_applicative_hom
      (MonadA (ArrowStrongM (KleisliArrowApply M))) (MonadA M)
      (KleisliRecoveryN M).
Proof.
  apply (fst (applicative_hom_equiv _ _ _ _ kleisli_applicative_triangle)).
  exact (applicative_hom_comp _ _ _ _ _ kleisli_applicative_hom
    (dynamic_applicative_hom (KleisliArrowApply M))).
Qed.

(** The same original Monad inverse preserves the recovered Applicative,
    even though recovery supplied canonical strength in place of the
    original choice. No strength records are identified. *)

(** 即使回收赋予规范强度而非原选定强度，同一个原 Monad 逆仍保持回收后的
    Applicative；不等同强度记录。 *)

Lemma kleisli_recovered_applicative_inverse_hom
  : is_applicative_hom (MonadA M)
      (MonadA (ArrowStrongM (KleisliArrowApply M)))
      (KleisliRecoveryInvN M).
Proof.
  exact (applicative_hom_inverse _ _ _ kleisli_recovered_applicative_hom
    (KleisliRecoveryNatIso M).2).
Qed.

End Comparison.
