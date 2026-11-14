From Cats.STLC Require Export Renaming.

(** * Partial Renaming and Removing an Unused Variable

    A partial renaming can refuse an unavailable variable. Its action on
    terms succeeds exactly when every requested variable is available.
    Under a binder, the new variable is always available and older
    variables follow the original partial assignment.

    This gives a transparent left inverse of weakening. In particular,
    weakening is injective on raw typed terms without any decision on
    base labels or uniqueness of identity proofs. This is useful when
    comparing the weakened functions in eta sources. *)

(** * 部分重命名与移除未使用变量

    部分重命名可以拒绝不可用变量。它对项的作用成功，当且仅当所需的每个变量
    均可用。进入绑定时，新变量总是可用，旧变量遵循原部分赋值。

    由此得到弱化的透明左逆。特别地，弱化对原始带类型项是单射，无须判定
    基标签或假定恒等证明唯一性。这可用于比较 η 来源中的弱化函数。 *)

Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Partial Variable Assignments

    Fix arbitrary base labels. Optional results retain available variables;
    failure carries no invented term or default variable. *)

(** ** 部分变量赋值

    固定任意基标签。可选结果保留可用变量；失败时不凭空提供项或默认变量。 *)

Section PartialAssignments.
Context {B : Type}.

(** A type-preserving partial assignment of variables. *)

(** 保持类型的部分变量赋值。 *)

Definition PartialRen (Δ Γ : Ctx B)
  : Type
  := ∀ A, Var Γ A → option (Var Δ A).

(** Compare partial assignments pointwise, without equality of functions. *)

(** 逐点比较部分赋值，不使用函数相等。 *)

Definition PartialRenEq {Γ Δ : Ctx B} (ρ τ : PartialRen Δ Γ)
  : Type
  := ∀ A x, ρ A x = τ A x.

Infix "≈PRen" := PartialRenEq
  (at level 50, no associativity) : stlc_ren_scope.

(** Pointwise equality is an equivalence relation. *)

(** 逐点相等是等价关系。 *)

Global Instance PartialRenEq_Equivalence {Γ Δ : Ctx B}
  : Equivalence (@PartialRenEq Γ Δ).
Proof.
  split.
  - intros ρ A x. reflexivity.
  - intros ρ τ h A x. symmetry. apply h.
  - intros ρ τ ν h k A x. transitivity (τ A x); [apply h | apply k].
Defined.

(** Lift under a binder, keeping the newest variable available. *)

(** 在绑定下提升，保持最新变量可用。 *)

Definition partial_ren_lift {Γ Δ : Ctx B} {A : Ty B}
    (ρ : PartialRen Δ Γ)
  : PartialRen (Δ ▻ A) (Γ ▻ A)
  := λ U x, match x with
      | inl y => option_map var_succ (ρ U y)
      | inr y => Some (inr y)
      end.

(** Binder lifting respects pointwise equality. *)

(** 绑定提升保持逐点相等。 *)

Global Instance partial_ren_lift_proper {Γ Δ : Ctx B} {A : Ty B}
  : Proper (PartialRenEq ==> PartialRenEq) (@partial_ren_lift Γ Δ A).
Proof.
  intros ρ τ h U [x | x]; cbn [partial_ren_lift].
  - rewrite h. reflexivity.
  - reflexivity.
Defined.

(** Structural action; failure of any child propagates to its parent. *)

(** 结构作用；任一子项的失败均传播至其父项。 *)

Fixpoint partial_rename {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ : Ctx B, PartialRen Δ Γ → option (Tm Δ A).
Proof.
  destruct t as [Γ A x | Γ | Γ A U t u | Γ A U t |
    Γ A U t | Γ A U t | Γ A U t u]; intros Δ ρ.
  - exact (option_map tm_var (ρ A x)).
  - exact (Some tm_unit).
  - exact (match partial_rename _ _ t Δ ρ,
        partial_rename _ _ u Δ ρ with
      | Some t', Some u' => Some (⟨t', u'⟩)
      | _, _ => None
      end).
  - exact (option_map tm_fst (partial_rename _ _ t Δ ρ)).
  - exact (option_map tm_snd (partial_rename _ _ t Δ ρ)).
  - exact (option_map tm_lam
      (partial_rename _ _ t (Δ ▻ A) (partial_ren_lift ρ))).
  - exact (match partial_rename _ _ t Δ ρ,
        partial_rename _ _ u Δ ρ with
      | Some t', Some u' => Some (t' · u')
      | _, _ => None
      end).
Defined.

(** Term action respects the specified equality of partial assignments. *)

(** 项作用保持部分赋值的指定相等。 *)

Lemma partial_rename_proper {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ (Δ : Ctx B) (ρ τ : PartialRen Δ Γ),
      ρ ≈PRen τ → partial_rename t Δ ρ = partial_rename t Δ τ.
Proof.
  induction t; intros Δ ρ τ h; cbn [partial_rename].
  - rewrite h. reflexivity.
  - reflexivity.
  - rewrite (IHt1 Δ ρ τ h), (IHt2 Δ ρ τ h). reflexivity.
  - rewrite (IHt Δ ρ τ h). reflexivity.
  - rewrite (IHt Δ ρ τ h). reflexivity.
  - rewrite (IHt (Δ ▻ A) _ _ (partial_ren_lift_proper _ _ h)).
    reflexivity.
  - rewrite (IHt1 Δ ρ τ h), (IHt2 Δ ρ τ h). reflexivity.
Defined.

(** Partial left inverses of renamings lift to partial left inverses
    under a fresh binder. This law is pointwise on variables. *)

(** 重命名的部分左逆在新绑定下仍提升为部分左逆。此律在变量上逐点成立。 *)

Lemma partial_ren_lift_inverse {Γ Δ : Ctx B} {A : Ty B}
    (ρ : Ren Δ Γ) (τ : PartialRen Γ Δ)
    (h : ∀ U x, τ U (ρ U x) = Some x)
  : ∀ U x, partial_ren_lift (A := A) τ U ((ρ^↑Ren) U x) = Some x.
Proof.
  intros U [x | x]; cbn [ren_lift partial_ren_lift].
  - rewrite h. reflexivity.
  - reflexivity.
Defined.

(** Variable-level partial inverses extend to every term. All recursive
    calls retain the actual context and result type of the child. *)

(** 变量层面的部分逆扩张到每个项。各递归调用保留子项实际的上下文与结果类型。 *)

Lemma partial_rename_inverse {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ (Δ : Ctx B) (ρ : Ren Δ Γ) (τ : PartialRen Γ Δ),
      (∀ U x, τ U (ρ U x) = Some x) →
      partial_rename t⟨ρ⟩ Γ τ = Some t.
Proof.
  induction t; intros Δ ρ τ h; cbn [rename partial_rename].
  - rewrite h. reflexivity.
  - reflexivity.
  - rewrite (IHt1 Δ ρ τ h), (IHt2 Δ ρ τ h). reflexivity.
  - rewrite (IHt Δ ρ τ h). reflexivity.
  - rewrite (IHt Δ ρ τ h). reflexivity.
  - rewrite (IHt (Δ ▻ A) (ρ^↑Ren) (partial_ren_lift τ)
      (partial_ren_lift_inverse ρ τ h)). reflexivity.
  - rewrite (IHt1 Δ ρ τ h), (IHt2 Δ ρ τ h). reflexivity.
Defined.

(** Refuse the newest variable, retaining every older variable. *)

(** 拒绝最新变量，保留全部旧变量。 *)

Definition partial_drop {Γ : Ctx B} {A : Ty B}
  : PartialRen Γ (Γ ▻ A)
  := λ U x, match x with inl y => Some y | inr _ => None end.

(** Removing a newly added unused variable recovers the original term. *)

(** 移除新增但未使用的变量可恢复原项。 *)

Definition partial_drop_weaken {Γ : Ctx B} {A U : Ty B} (t : Tm Γ U)
  : partial_rename t⟨@ren_weaken B Γ A⟩ Γ partial_drop = Some t
  := partial_rename_inverse t _ wkRen partial_drop (λ V x, eq_refl).

(** Injectivity follows by applying the same partial inverse to both
    terms. This does not require comparing index paths. *)

(** 对两项作用同一个部分逆即得单射性，不需要比较索引路径。 *)

Definition rename_weaken_injective {Γ : Ctx B} {A U : Ty B}
    (t u : Tm Γ U) (h : t⟨@ren_weaken B Γ A⟩ = u⟨wkRen⟩)
  : t = u.
Proof.
  pose proof (f_equal
    (λ v : Tm (Γ ▻ A) U, partial_rename v Γ (@partial_drop Γ A)) h) as k.
  change (partial_rename t⟨@ren_weaken B Γ A⟩ Γ partial_drop =
    partial_rename u⟨@ren_weaken B Γ A⟩ Γ partial_drop) in k.
  rewrite (partial_drop_weaken (A := A) t),
    (partial_drop_weaken (A := A) u) in k.
  now injection k.
Defined.

End PartialAssignments.
