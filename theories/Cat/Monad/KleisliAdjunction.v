From Cats Require Export
  Cat.Monad.Kleisli
  Cat.Monad.Adjunction
  Cat.Monad.Category
  Cat.Adjunction.

Local Open Scope monad_scope.

(** * The Kleisli Adjunction and Recovery of the Monad

    The two hom-sets in the adjunction are the same base hom-set. Its
    identity correspondence gives the adjunction, and the existing general
    construction recovers the original Monad up to a Monad isomorphism.
    No strength, products or closed structure are needed. *)

(** * Kleisli 伴随及 Monad 的恢复

    伴随两侧的 Hom 广集就是同一个基底 Hom 广集，恒等对应给出伴随。
    已有一般构造恢复原 Monad，比较为 Monad 同构。不需要强度、积或闭结构。 *)

Section KleisliAdjunction.
Context {C : Cat} (M : Monad C).

(** Reuse the general construction from mutually inverse respectful hom
    maps. Naturality in the source is pure substitution; naturality in the
    target is the definition of Kleisli composition. *)

(** 复用互逆保相等 Hom 映射的一般伴随构造。来源自然性就是纯值代入，目标
    自然性就是 Kleisli 复合的定义。 *)

Program Definition KleisliAdjunction
  : KleisliPureF M ⊣ KleisliExtendF M
  := AdjunctionFromHom (KleisliPureF M) (KleisliExtendF M)
      (λ X Y, id_resp) (λ X Y, id_resp) _ _ _ _.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. exact (kleisli_comp_pure_r M f h). Defined.
Next Obligation. reflexivity. Defined.

(** Transposition retains the underlying computation unchanged. *)

(** 转置保持底层计算不变。 *)

Lemma kleisli_adjunct {X Y : @Ob C} (f : Hom X (M Y))
  : f^♯[KleisliAdjunction] ≈ f.
Proof. reflexivity. Qed.

(** Inverse transposition also retains the computation. *)

(** 逆转置也保持计算不变。 *)

Lemma kleisli_unadjunct {X Y : @Ob C} (f : Hom X (M Y))
  : (f^♭[KleisliAdjunction] : Hom X (M Y)) ≈ f.
Proof. reflexivity. Qed.

(** The unit is the original Monad unit, by transposing a Kleisli identity. *)

(** 单位是原 Monad 单位，由转置 Kleisli 恒等得到。 *)

Lemma kleisli_adjunction_unit (X : @Ob C)
  : adjunction_unit KleisliAdjunction X ≈ η[M] X.
Proof. reflexivity. Qed.

(** The counit at [X] is the base identity on [M X], viewed as a Kleisli
    arrow from [M X] to [X]. *)

(** [X] 处的余单位是 [M X] 上的基底恒等，视为从 [M X] 到 [X] 的 Kleisli 箭头。 *)

Lemma kleisli_adjunction_counit (X : @Ob C)
  : (adjunction_counit KleisliAdjunction X : Hom (M X) (M X)) ≈ id.
Proof. reflexivity. Qed.

(** The left triangle uses Kleisli composition and its identity. The proof
    is inherited from the general hom-correspondence theory. *)

(** 左三角使用 Kleisli 复合及其恒等，证明继承自一般 Hom 对应理论。 *)

Lemma kleisli_adjunction_triangle_l (X : @Ob C)
  : adjunction_counit KleisliAdjunction X ∘K[M]
      return[M; adjunction_unit KleisliAdjunction X] ≈ η[M] X.
Proof. exact (adjunction_triangle_l KleisliAdjunction X). Qed.

(** The right triangle takes place in the base category. *)

(** 右三角在基底范畴中成立。 *)

Lemma kleisli_adjunction_triangle_r (X : @Ob C)
  : kleisli_extend M (adjunction_counit KleisliAdjunction X) ∘
      adjunction_unit KleisliAdjunction (M X) ≈ id.
Proof. exact (adjunction_triangle_r KleisliAdjunction X). Qed.

(** Use the general adjunction-to-Monad construction without reproving its
    laws for this particular category. *)

(** 使用一般伴随到 Monad 构造，不为此具体范畴重新证明其定律。 *)

Definition KleisliMonad
  : Monad C
  := AdjunctionMonad KleisliAdjunction.

(** The recovered unit is the original unit. *)

(** 恢复后的单位就是原单位。 *)

Lemma kleisli_monad_unit (X : @Ob C)
  : η[KleisliMonad] X ≈ η[M] X.
Proof. exact (kleisli_adjunction_unit X). Qed.

(** Extending the identity computation recovers the original multiplication. *)

(** 扩张恒等计算，恢复原乘法。 *)

Lemma kleisli_monad_mul (X : @Ob C)
  : μ[KleisliMonad] X ≈ μ[M] X.
Proof.
  change (kleisli_extend M (@id (M X)) ≈ μ[M] X).
  unfold kleisli_extend. rewrite functor_id, comp_id_r. reflexivity.
Qed.

(** The existing comparison of underlying functors preserves both Monad
    operations, so it is an actual fixed-base Monad morphism. *)

(** 已有底层函子比较保持两个 Monad 运算，因此是实际的固定基底 Monad 态射。 *)

Program Definition KleisliMonadTo
  : MonadHomS KleisliMonad M
  := ((KleisliCompositeIso M).1; _).
Next Obligation.
  split; intros X.
  - change (id ∘ η[KleisliMonad] X ≈ η[M] X).
    rewrite comp_id_l. apply kleisli_monad_unit.
  - change (id ∘ μ[KleisliMonad] X ≈
      μ[M] X ∘ (id ∘ fmap KleisliMonad (@id (M X)))).
    rewrite functor_id, !comp_id_l, comp_id_r. apply kleisli_monad_mul.
Defined.

(** The inverse natural comparison also preserves unit and multiplication. *)

(** 逆向自然比较也保持单位及乘法。 *)

Program Definition KleisliMonadFrom
  : MonadHomS M KleisliMonad
  := (NatIso_inv (KleisliCompositeIso M).1 (KleisliCompositeIso M).2; _).
Next Obligation.
  split; intros X.
  - change (id ∘ η[M] X ≈ η[KleisliMonad] X).
    rewrite comp_id_l. symmetry. apply kleisli_monad_unit.
  - change (id ∘ μ[M] X ≈
      μ[KleisliMonad] X ∘ (id ∘ fmap M (@id (M X)))).
    rewrite functor_id, !comp_id_l, comp_id_r.
    symmetry. apply kleisli_monad_mul.
Defined.

(** Recovery is an isomorphism in the existing category of Monads, not
    native equality of structures or their law witnesses. *)

(** 恢复给出已有 Monad 范畴中的同构，不使用结构或其定律见证的原生相等。 *)

Program Definition KleisliMonadIso
  : KleisliMonad ≅[MonadCat C] M
  := (KleisliMonadTo; (KleisliMonadFrom; _)).
Next Obligation.
  split; intros X; change ((@id (M X)) ∘ id ≈ id); apply comp_id_l.
Defined.

End KleisliAdjunction.
