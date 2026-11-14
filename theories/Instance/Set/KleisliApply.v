From Cats Require Export
  Cat.Computational.Arrow.Apply
  Cat.Computational.Arrow.Kleisli.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid
  Instance.Set.Strength.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope computation_scope.
Local Open Scope monad_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * Dynamic Evaluation of Kleisli Computations

    Fix a strong Monad on setoids at a common carrier/equality bound.
    Its native Kleisli Hom setoids can then be ordinary input values.
    Evaluation needs no new structure on the Monad: apply the respectful
    computation to its input. The three ArrowApply laws reuse ordinary
    Kleisli extension and the pointwise formula for any supplied strength. *)

(** * Kleisli 计算的动态求值

    固定共同载体／相等界上的广集强 Monad，使原生 Kleisli Hom 广集可以作为
    通常输入值。求值不为 Monad 增加结构：将保相等计算作用于输入即可。
    三条 ArrowApply 定律复用通常 Kleisli 扩张及任意所给强度的逐点公式。 *)

Section Kleisli.
Universe u.
Context (M : StrongMonad (SetCat@{u u _ _ _ _ _}) SetCartesianMonoidal).

(** Run a supplied Kleisli arrow without adding another effect. Its result
    already lies in the original Monad. *)

(** 运行所给 Kleisli 箭头，不附加另一层效应；结果已经位于原 Monad 中。 *)

Program Definition kleisli_apply (X Y : SetC@{u u})
  : (HomSet (Cat := KleisliCat M) X Y ×S X) →r M Y
  :=
  {|func p := fst p (snd p)
  |}.
Next Obligation.
  intros [f x] [g y] [Hf Hx].
  transitivity (g x); [exact (Hf x) | apply func_proper; exact Hx].
Defined.

(** Dynamic application extends the exact existing Kleisli Arrow. The
    chosen strength is not replaced by a particular model implementation. *)

(** 动态应用扩充恰好已有的 Kleisli Arrow；不将选定强度替换为某个具体模型实现。 *)

Program Definition KleisliArrowApply
  : ArrowApply (KleisliCat M)
  :=
  {|ArrowApplyA := KleisliArrow M
  ; arrow_apply X Y := kleisli_apply X Y
  |}.
Next Obligation.
  change (kleisli_apply Y (X ×S Y) ∘K[M]
    return[M; arrow_apply_pair (KleisliArrow M) X Y × id_resp] ≈
    η[M] (X ×S Y)).
  rewrite kleisli_comp_pure_r. intros [x y]. reflexivity.
Defined.
Next Obligation.
  change (kleisli_apply X Z ∘K[M]
    return[M; comp_r_resp (C := KleisliCat M) (f := g) × id_resp] ≈
    kleisli_apply Y Z ∘K[M]
      kleisli_context M (HomSet (Cat := KleisliCat M) Y Z) g).
  rewrite kleisli_comp_pure_r. intros [f x].
  change (kleisli_extend M f (g x) ≈S
    kleisli_extend M (kleisli_apply Y Z)
      (kleisli_context M (HomSet (Cat := KleisliCat M) Y Z) g (f,x))).
  etransitivity.
  - exact (@kleisli_extend_proper SetCat M _ _ f
      (kleisli_apply Y Z ∘ ⟨const_resp Y f, id⟩)
      (λ y, reflexivity _) (g x)).
  - etransitivity.
    + exact (@kleisli_extend_pre SetCat M _ _ _ (kleisli_apply Y Z)
        ⟨const_resp Y f, id⟩ (g x)).
    + apply (@func_proper
        (M (HomSet (Cat := KleisliCat M) Y Z ×S Y)) (M Z)
        (kleisli_extend M (kleisli_apply Y Z)) _ _). symmetry.
      change (strengthN (hasStrength M)
        (HomSet (Cat := KleisliCat M) Y Z, Y) (f,g x) ≈S
        fmap M ⟨const_resp Y f, id⟩ (g x)).
      apply set_strength_value.
Defined.
Next Obligation.
  change (kleisli_apply X Z ∘K[M]
    return[M; comp_l_resp (C := KleisliCat M) (f := h) × id_resp] ≈
    h ∘K[M] kleisli_apply X Y).
  rewrite kleisli_comp_pure_r. intros [f x]. reflexivity.
Defined.

(** The public application notation is the supplied computation itself
    at the given input. All computational data remain transparent. *)

(** 公开应用记号在给定输入处就是所给计算本身，全部计算数据保持透明。 *)

Lemma kleisli_apply_value {X Y : SetC@{u u}}
    (f : X →r M Y) (x : X)
  : apply[KleisliArrowApply; X; Y] (f,x) ≈S f x.
Proof. reflexivity. Qed.

End Kleisli.
