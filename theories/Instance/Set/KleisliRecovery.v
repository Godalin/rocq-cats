From Cats Require Export
  Cat.Computational.Arrow.Monad
  Cat.Monad.Category
  Instance.Set.KleisliApply.
From Cats Require Import
  Cat.Isomorphism
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope computation_scope.
Local Open Scope monad_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * Recovering a Monad from Its Kleisli ArrowApply

    Fix a strong Monad on native setoids at a common carrier/equality bound,
    as required by the existing Kleisli ArrowApply model. Evaluate recovered
    global computations at the singleton to obtain a transparent natural
    isomorphism. Both directions preserve unit and multiplication, giving
    an isomorphism of Monads, with no new laws on the supplied strength. *)

(** * 从 Kleisli ArrowApply 回收 Monad

    固定原生广集上的强 Monad，使用已有 Kleisli ArrowApply 模型所要求的共同
    载体／相等界。在单元素处求值回收后的全局计算，得到透明自然同构。
    双向均保持单位及乘法，给出 Monad 同构，不为所给强度添加新定律。 *)

Section Recovery.
Universe u.
Context (M : StrongMonad (SetCat@{u u _ _ _ _ _}) SetCartesianMonoidal).

(** Recover a Monad from the existing Kleisli ArrowApply, using the general
    dynamic adjunction construction. *)

(** 通过一般动态伴随构造，从已有 Kleisli ArrowApply 回收 Monad。 *)

Definition KleisliRecoveredM
  : Monad (SetCat@{u u _ _ _ _ _})
  := ArrowMonad (KleisliArrowApply M).

(** Evaluate the terminal-input computation. Naturality uses the existing
    pure-result mapping law for Kleisli composition. *)

(** 求值终端输入的计算；自然性使用已有 Kleisli 复合的纯结果映射定律。 *)

Program Definition KleisliRecoveryN
  : KleisliRecoveredM ⇒ M
  :=
  {|nt X := {|func m := m tt
            |}
  |}.
Next Obligation. intros m n E. exact (E tt). Defined.

Next Obligation.
  intros m.
  change ((return[M; f] ∘K[M] m) tt ≈S fmap M f (m tt)).
  exact (kleisli_comp_pure_l M f m tt).
Defined.

(** The inverse makes an original monadic value into a constant computation.
    It adds no effect and uses no Monad unit. *)

(** 逆映射将原 Monad 值做成常值计算，不增加效应，也不使用 Monad 单位。 *)

Program Definition KleisliRecoveryInvN
  : M ⇒ KleisliRecoveredM
  :=
  {|nt X := {|func m := const_resp UnitS m
            |}
  |}.
Next Obligation. intros m n E t. exact E. Defined.

Next Obligation.
  intros m []. symmetry. exact (kleisli_comp_pure_l M f
    (const_resp UnitS m) tt).
Defined.

(** The recovered and original functors are naturally isomorphic in the
    specified setoid equality, without equality of structure records. *)

(** 回收与原函子在指定广集相等下自然同构，不要求结构记录相等。 *)

Program Definition KleisliRecoveryNatIso
  : KleisliRecoveredM ≅N M
  := (KleisliRecoveryN; _).
Next Obligation.
  intros X. exists (KleisliRecoveryInvN X).
  split; [intros m [] | intros m]; reflexivity.
Defined.

(** An abstract left inverse law avoids reducing large computed witnesses
    when a client uses recovery. *)

(** 抽象左逆律使客户端使用回收时无需归约大型计算见证。 *)

Lemma kleisli_recovery_inv_l (X : SetC@{u u})
    (m : KleisliRecoveredM X)
  : KleisliRecoveryInvN X (KleisliRecoveryN X m) ≈S m.
Proof. intros []. reflexivity. Qed.

(** Evaluation cancels the constant-computation inverse on original values. *)

(** 对原有值，求值消去常值计算逆映射。 *)

Lemma kleisli_recovery_inv_r (X : SetC@{u u}) (m : M X)
  : KleisliRecoveryN X (KleisliRecoveryInvN X m) ≈S m.
Proof. reflexivity. Qed.

(** Dynamic evaluation is the ordinary value-indexed Kleisli computation. *)

(** 动态求值就是通常的值索引 Kleisli 计算。 *)

Lemma kleisli_recovery_eval {X Y : SetC@{u u}}
    (f : X →r KleisliRecoveredM Y)
  : arrow_dynamic_eval (KleisliArrowApply M) f ≈
    KleisliRecoveryN Y ∘ f.
Proof.
  change (kleisli_apply M UnitS Y ∘K[M]
    return[M; ⟨f,!⟩] ≈ KleisliRecoveryN Y ∘ f).
  rewrite kleisli_comp_pure_r. intros x. reflexivity.
Qed.

(** The dynamic adjunction counit evaluates a global computation. *)

(** 动态伴随的余单位求值全局计算。 *)

Lemma kleisli_recovery_counit (X : SetC@{u u})
  : arrow_dynamic_eval (KleisliArrowApply M)
      (id_resp (X := KleisliRecoveredM X)) ≈ KleisliRecoveryN X.
Proof.
  etransitivity; [apply kleisli_recovery_eval |].
  exact (@comp_id_r SetCat _ _ (KleisliRecoveryN X)).
Qed.

(** Recovery preserves continuation extension and its effect order. *)

(** 回收保持续延扩张及其效应次序。 *)

Lemma kleisli_recovery_extend {X Y : SetC@{u u}}
    (f : X →r KleisliRecoveredM Y)
  : KleisliRecoveryN Y ∘ kleisli_extend KleisliRecoveredM f ≈
    kleisli_extend M (KleisliRecoveryN Y ∘ f) ∘ KleisliRecoveryN X.
Proof.
  intros m.
  change (kleisli_extend M (arrow_dynamic_eval (KleisliArrowApply M)
    (id_resp (X := KleisliRecoveredM Y)))
      ((return[M; f] ∘K[M] m) tt) ≈S
    kleisli_extend M (KleisliRecoveryN Y ∘ f) (m tt)).
  transitivity (kleisli_extend M (KleisliRecoveryN Y)
    ((return[M; f] ∘K[M] m) tt)).
  - exact (@kleisli_extend_proper SetCat M _ _ _ _
      (kleisli_recovery_counit Y) _).
  - transitivity (kleisli_extend M (KleisliRecoveryN Y)
      (fmap M f (m tt))).
    + apply (@func_proper _ _ (kleisli_extend M (KleisliRecoveryN Y))).
      exact (kleisli_comp_pure_l M f m tt).
    + symmetry. exact (kleisli_extend_pre M (KleisliRecoveryN Y) f (m tt)).
Qed.

(** The forward comparison preserves the original Monad unit. *)

(** 正向比较保持原 Monad 单位。 *)

Lemma kleisli_recovery_unit (X : SetC@{u u})
  : KleisliRecoveryN X ∘ η[KleisliRecoveredM] X ≈ η[M] X.
Proof.
  intros x. exact (arrow_monad_unit (KleisliArrowApply M) X x tt).
Qed.

(** The forward comparison preserves multiplication with the required
    horizontal natural-transformation composite. *)

(** 正向比较保持乘法，使用所需的自然变换水平复合。 *)

Lemma kleisli_recovery_mul (X : SetC@{u u})
  : KleisliRecoveryN X ∘ μ[KleisliRecoveredM] X ≈
    μ[M] X ∘ (KleisliRecoveryN ∘Nh KleisliRecoveryN) X.
Proof.
  intros m.
  change (kleisli_extend M (arrow_dynamic_eval (KleisliArrowApply M)
    (id_resp (X := KleisliRecoveredM X))) (m tt) ≈S
    μ[M] X ((return[M; KleisliRecoveryN X] ∘K[M] m) tt)).
  transitivity (kleisli_extend M (KleisliRecoveryN X) (m tt)).
  - exact (@kleisli_extend_proper SetCat M _ _ _ _
      (kleisli_recovery_counit X) (m tt)).
  - symmetry. apply (@func_proper _ _ (μ[M] X)).
    exact (kleisli_comp_pure_l M (KleisliRecoveryN X) m tt).
Qed.

(** Package the forward comparison as a fixed-base Monad morphism. *)

(** 将正向比较打包为固定基底 Monad 态射。 *)

Program Definition KleisliRecoveryTo
  : MonadHomS KleisliRecoveredM M
  := (KleisliRecoveryN; _).
Next Obligation.
  split; [exact kleisli_recovery_unit | exact kleisli_recovery_mul].
Defined.

(** The constant-computation inverse also preserves the Monad unit. *)

(** 常值计算逆映射也保持 Monad 单位。 *)

Lemma kleisli_recovery_inverse_unit (X : SetC@{u u})
  : KleisliRecoveryInvN X ∘ η[M] X ≈ η[KleisliRecoveredM] X.
Proof.
  intros x []. symmetry.
  exact (arrow_monad_unit (KleisliArrowApply M) X x tt).
Qed.

(** The inverse preserves multiplication by functor composition and the
    evaluation/constant inverse law; no effect commutation is assumed. *)

(** 由函子复合及求值／常值互逆律，逆映射保持乘法；不假设效应交换。 *)

Lemma kleisli_recovery_inverse_mul (X : SetC@{u u})
  : KleisliRecoveryInvN X ∘ μ[M] X ≈
    μ[KleisliRecoveredM] X ∘ (KleisliRecoveryInvN ∘Nh KleisliRecoveryInvN) X.
Proof.
  intros m [].
  change (μ[M] X m ≈S
    kleisli_extend M (arrow_dynamic_eval (KleisliArrowApply M)
      (id_resp (X := KleisliRecoveredM X)))
      (fmap M (KleisliRecoveryInvN X) m)).
  symmetry. transitivity (kleisli_extend M (KleisliRecoveryN X)
    (fmap M (KleisliRecoveryInvN X) m)).
  - exact (@kleisli_extend_proper SetCat M _ _ _ _
      (kleisli_recovery_counit X) _).
  - change (μ[M] X (fmap M (KleisliRecoveryN X)
      (fmap M (KleisliRecoveryInvN X) m)) ≈S μ[M] X m).
    apply (@func_proper _ _ (μ[M] X)).
    transitivity (fmap M (KleisliRecoveryN X ∘ KleisliRecoveryInvN X) m).
    + symmetry. exact (@functor_comp SetCat SetCat M _ _ _
        (KleisliRecoveryN X) (KleisliRecoveryInvN X) m).
    + transitivity (fmap M (@id (M X)) m).
      * assert (E : KleisliRecoveryN X ∘ KleisliRecoveryInvN X ≈
          @id (M X)) by (intros v; reflexivity).
        exact (@functor_fmap_proper SetCat SetCat M _ _ _ _ E m).
      * exact (@functor_id SetCat SetCat M (M X) m).
Qed.

(** Package the inverse comparison as a fixed-base Monad morphism. *)

(** 将逆向比较打包为固定基底 Monad 态射。 *)

Program Definition KleisliRecoveryFrom
  : MonadHomS M KleisliRecoveredM
  := (KleisliRecoveryInvN; _).
Next Obligation.
  split; [exact kleisli_recovery_inverse_unit |
    exact kleisli_recovery_inverse_mul].
Defined.

(** The two Monad morphisms are inverse in the existing Monad category.
    This recovers the Monad from its Kleisli ArrowApply, rather than claiming
    a reconstruction theorem for every ArrowApply structure. *)

(** 两个 Monad 态射在已有 Monad 范畴中互逆。这从 Kleisli ArrowApply 回收
    Monad，并不宣称每个 ArrowApply 结构的重建定理。 *)

Program Definition KleisliRecoveryIso
  : KleisliRecoveredM ≅[MonadCat SetCat] M
  := (KleisliRecoveryTo; (KleisliRecoveryFrom; _)).
Next Obligation.
  split; intros X; [intros m [] | intros m]; reflexivity.
Defined.

End Recovery.
