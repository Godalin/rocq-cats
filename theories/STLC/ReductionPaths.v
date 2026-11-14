From Cats.STLC Require Export Reduction.
From Cats.Set.Relation Require Import Compatible.

(** * Substitution Paths for Compatible Term Relations

    An argument step may be duplicated or discarded by substitution.
    Work with finite paths for an arbitrary term relation preserved by
    constructors and renaming. The same structural argument applies to
    beta, eta contraction and their sum. *)

(** * 相容项关系的替换路径

    替换可能复制或丢弃实参步骤。对由构造器及重命名保持的任意项关系，使用
    有限路径处理这一现象。同一个结构论证适用于 β、η 收缩及其和。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Constructor and Assignment Paths

    Fix a term relation, its constructor compatibility and preservation
    by renaming. Path evidence at [p] is independent of the relation's
    classification bound [l]. No equation between assignments is needed. *)

(** ** 构造器与赋值路径

    固定项关系、其构造器相容性及重命名保持性。[p] 处的路径证据独立于关系
    的分类界 [l]，无须赋值之间的方程。 *)

Section TermPaths.
Universes b e p l.
Context {B : Type@{b}} (R : TmRelation@{b e l} B).
Context (compatible : is_compatible (TmContexts B) (tm_relation_family R)).

(** A one-hole operation acts on each edge of a finite path. *)

(** 单孔操作作用于有限路径的每一条边。 *)

Definition tm_rtc_lift {Γ Δ : Ctx B} {A U : Ty B}
    (c : TmOperation (Γ, A) (Δ, U)) {t u : Tm Γ A}
    (h : ReflTransClosure@{b e p} (R Γ A) t u)
  : ReflTransClosure@{b e p} (R Δ U)
      (TmContexts B _ _ c t) (TmContexts B _ _ c u)
  := rtc_preserves (TmContexts B _ _ c)
      (λ x y k, rtc_step (compatible _ _ c x y k)) h.

Context (rename_steps : ∀ Γ A (t u : Tm Γ A), R Γ A t u →
  ∀ Δ (ρ : Ren Δ Γ), R Δ A t⟨ρ⟩ u⟨ρ⟩).

(** Old assignments are weakened; the fresh variable has an empty path. *)

(** 旧赋值作弱化；新鲜变量具有空路径。 *)

Definition sub_lift_rtc {Γ Δ : Ctx B} {A : Ty B} {σ τ : Sub Δ Γ}
    (h : ∀ U x, ReflTransClosure@{b e p} (R Δ U) (σ U x) (τ U x))
  : ∀ U x, ReflTransClosure@{b e p} (R (Δ ▻ A) U)
      ((σ^↑Sub) U x) ((τ^↑Sub) U x).
Proof.
  intros U [x | x]; cbn.
  - exact (rtc_preserves (λ t, t⟨wkRen⟩)
      (λ t u k, rtc_step (rename_steps Δ U t u k _ wkRen)) (h U x)).
  - exact (rtc_refl _).
Defined.

(** Structural induction follows every occurrence of every assignment,
    retaining repeated paths rather than identifying their witnesses. *)

(** 结构归纳沿每个赋值的每次出现前进，保留重复路径，不识别其见证。 *)

Definition subst_rtc {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (σ τ : Sub Δ Γ),
      (∀ U x, ReflTransClosure@{b e p} (R Δ U) (σ U x) (τ U x)) →
      ReflTransClosure@{b e p} (R Δ A) t[σ] t[τ].
Proof.
  induction t; intros Δ σ τ h; cbn.
  - exact (h A v).
  - exact (rtc_refl _).
  - exact (rtc_trans (tm_rtc_lift (op_pair_l t2[σ]) (IHt1 Δ σ τ h))
      (tm_rtc_lift (op_pair_r t1[τ]) (IHt2 Δ σ τ h))).
  - exact (tm_rtc_lift op_fst (IHt Δ σ τ h)).
  - exact (tm_rtc_lift op_snd (IHt Δ σ τ h)).
  - exact (tm_rtc_lift op_lam
      (IHt _ (σ^↑Sub) (τ^↑Sub) (sub_lift_rtc h))).
  - exact (rtc_trans (tm_rtc_lift (op_app_l t2[σ]) (IHt1 Δ σ τ h))
      (tm_rtc_lift (op_app_r t1[τ]) (IHt2 Δ σ τ h))).
Defined.

(** A path in the newest argument induces a path after its substitution,
    including the cases of unused and repeated variables. *)

(** 最新实参中的路径在代入后诱导路径，包括变量未使用及重复使用的情形。 *)

Definition tm_rtc_single {Γ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U) {u u' : Tm Γ A}
    (h : ReflTransClosure@{b e p} (R Γ A) u u')
  : ReflTransClosure@{b e p} (R Γ U) t[u/] t[u'/].
Proof.
  apply subst_rtc. intros V [x | x]; cbn.
  - exact (rtc_refl _).
  - destruct x. exact h.
Defined.

End TermPaths.
