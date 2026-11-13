From Cats.STLC Require Import ReductionSubstitution.
From Cats.Set.Relation Require Import Compatible.

(** * Directed Beta Interface Regressions

    Check the generic substitution fold at unequal source/target witness
    levels and beta preservation at distinct and equal syntax/step levels.
    Concrete paths exercise duplication, discarded inputs, binding and
    variable identification, without a decision procedure for type labels. *)

(** * 有向 β 接口回归检查

    在不同的源／目标见证层级检查一般替换折叠，并在语法／步骤层级分离或相等时
    检查 β 保持性。具体路径涵盖复制、丢弃输入、绑定及变量识别，无须类型标签
    的判定过程。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Larger Target Witnesses

    Fix [b < r < s], arbitrary root systems and a substituted-generator
    interpreter. The context fold must preserve these distinct sizes. *)

(** ** 较大的目标见证

    固定 [b < r < s]、任意根系统及替换后生成元的解释器。上下文折叠须保持
    这些分离的大小。 *)

Section LargerTarget.
Universes b r s.
Constraint b < r, r < s.
Context {B : Type@{b}}.
Context (R : TmRelation@{b r _} B) (S : TmRelation@{b s _} B).
Context (hr : ∀ Γ A (t u : Tm Γ A), R Γ A t u →
  ∀ Δ (σ : Sub Δ Γ), ContextStep S t[σ] u[σ]).

(** Generic contextual preservation accepts strictly larger target edges. *)

(** 一般上下文保持性接受严格更大的目标边。 *)

Definition context_subst_larger_target {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : ContextStep R t u)
    (Δ : Ctx B) (σ : Sub Δ Γ)
  : ContextStep S t[σ] u[σ]
  := context_step_subst R S hr h Δ σ.

End LargerTarget.

(** ** Smaller Target Witnesses

    Reverse the edge-size order to [b < s < r]. The fold transforms given
    source evidence; it need not retain that evidence in the target. *)

(** ** 较小的目标见证

    将边的大小顺序反转为 [b < s < r]。折叠转换已有源证据，无须在目标中保存
    原证据。 *)

Section SmallerTarget.
Universes b r s.
Constraint b < s, s < r.
Context {B : Type@{b}}.
Context (R : TmRelation@{b r _} B) (S : TmRelation@{b s _} B).
Context (hr : ∀ Γ A (t u : Tm Γ A), R Γ A t u →
  ∀ Δ (σ : Sub Δ Γ), ContextStep S t[σ] u[σ]).

(** No spurious source-to-target universe bound is imposed. *)

(** 不施加多余的源到目标宇宙界限。 *)

Definition context_subst_smaller_target {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : ContextStep R t u)
    (Δ : Ctx B) (σ : Sub Δ Γ)
  : ContextStep S t[σ] u[σ]
  := context_step_subst R S hr h Δ σ.

End SmallerTarget.

(** ** Beta Evidence above Syntax

    Fix [b < e < p] and arbitrary base labels. Check large beta evidence,
    a still larger path bound, and pointwise assignment reduction. *)

(** ** 高于语法的 β 证据

    固定 [b < e < p] 及任意基类型标签。检查大 β 证据、更大的路径界，以及
    逐点赋值归约。 *)

Section SeparatedLevels.
Universes b e p.
Constraint b < e, e < p.
Context {B : Type@{b}} {Γ Δ : Ctx B} {A : Ty B}.

(** Root substitution keeps the larger evidence bound. *)

(** 根替换保持较大的证据界。 *)

Definition separated_root_subst {t u : Tm Γ A}
    (h : RootBeta@{b e _} t u) (σ : Sub Δ Γ)
  : RootBeta@{b e _} t[σ] u[σ]
  := root_beta_subst h Δ σ.

(** The same check for full contexts includes non-root occurrences. *)

(** 完整上下文的同类检查涵盖非根位置。 *)

Definition separated_step_subst {t u : Tm Γ A}
    (h : BetaStep@{b e _ _} t u) (σ : Sub Δ Γ)
  : BetaStep@{b e _ _} t[σ] u[σ]
  := beta_step_subst h Δ σ.

(** Renaming does not collapse the edge universe to syntax. *)

(** 重命名不将边宇宙压到语法层级。 *)

Definition separated_step_rename {t u : Tm Γ A}
    (h : BetaStep@{b e _ _} t u) (ρ : Ren Δ Γ)
  : BetaStep@{b e _ _} t⟨ρ⟩ u⟨ρ⟩
  := beta_step_rename h Δ ρ.

(** Path substitution keeps a bound strictly above the individual edges. *)

(** 路径替换保持严格高于单条边的界。 *)

Definition separated_path_subst {t u : Tm Γ A}
    (h : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Γ A) t u)
    (σ : Sub Δ Γ)
  : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Δ A) t[σ] u[σ]
  := beta_rtc_subst h Δ σ.

(** The generic one-hole lift can change context and result type. *)

(** 一般单孔提升可以改变上下文与结果类型。 *)

Definition separated_path_lift {U : Ty B}
    (c : TmOperation (Γ, A) (Δ, U)) {t u : Tm Γ A}
    (h : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Γ A) t u)
  : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Δ U)
      (TmContexts B (Γ, A) (Δ, U) c t)
      (TmContexts B (Γ, A) (Δ, U) c u)
  := beta_rtc_lift c h.

(** Assignment reduction also accepts beta evidence above syntax. *)

(** 赋值归约同样接受高于语法的 β 证据。 *)

Definition separated_assignment_path (t : Tm Γ A) (σ τ : Sub Δ Γ)
    (h : ∀ U x, ReflTransClosure@{b e p}
      (@BetaStep@{b e _ _} B Δ U) (σ U x) (τ U x))
  : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Δ A) t[σ] t[τ]
  := subst_beta_rtc t Δ σ τ h.

(** Both a term path and its assignment paths can use the larger bound. *)

(** 项路径及其赋值路径可以共同使用较大的界。 *)

Definition separated_both_path {t u : Tm Γ A}
    (h : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Γ A) t u)
    {σ τ : Sub Δ Γ}
    (k : ∀ U x, ReflTransClosure@{b e p}
      (@BetaStep@{b e _ _} B Δ U) (σ U x) (τ U x))
  : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Δ A) t[σ] u[τ]
  := beta_rtc_subst_both h k.

(** Single-variable replacement also retains the larger path universe. *)

(** 单变量代入同样保留较大的路径宇宙。 *)

Definition separated_single_path {U : Ty B} (t : Tm (Γ ▻ A) U)
    {u v : Tm Γ A}
    (h : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Γ A) u v)
  : ReflTransClosure@{b e p} (@BetaStep@{b e _ _} B Γ U) t[u/] t[v/]
  := beta_rtc_single t h.

End SeparatedLevels.

(** ** Equal Syntax and Evidence Levels

    Fix an arbitrary signature at one common level; strict separation is
    not required by the interface. *)

(** ** 相同的语法与证据层级

    在共同层级固定任意签名；接口并不要求严格分离。 *)

Section EqualLevels.
Universe b.
Context {B : Type@{b}} {Γ Δ : Ctx B} {A : Ty B}.

(** Full-step preservation permits the equal-level instance. *)

(** 完整步骤的保持性允许同层实例。 *)

Definition equal_level_step_subst {t u : Tm Γ A}
    (h : BetaStep@{b b _ _} t u) (σ : Sub Δ Γ)
  : BetaStep@{b b _ _} t[σ] u[σ]
  := beta_step_subst h Δ σ.

End EqualLevels.

(** ** Concrete Directed Paths

    Work over the empty base signature, using unit and function/product
    types. Measure the number of contextual beta edges, not the size of
    their evidence or the length of an equational conversion. *)

(** ** 具体有向路径

    在空基签名上使用单位、函数及积类型。测量的是上下文 β 边的数量，不是
    证据大小或等式转换长度。 *)

Section Computations.

(** A closed beta redex with unit result. *)

(** 结果为单位的闭 β 可归约式。 *)

Definition unit_redex
  : Tm (∅ : Ctx Empty_set) ⊤
  := (ƛ (# var_zero)) · ⋆.

(** Its contraction supplies a one-edge directed path. *)

(** 其收缩给出单边有向路径。 *)

Definition unit_redex_path
  : ((@BetaStep Empty_set ∅ ⊤)^*) unit_redex ⋆
  := rtc_step (context_step_root _ (root_beta_function (# var_zero) ⋆)).

(** This test observation counts edges in a unit-typed beta path. *)

(** 这个测试观测函数计算单位类型 β 路径中的边数。 *)

Fixpoint unit_beta_length {Γ : Ctx Empty_set} {t u : Tm Γ ⊤}
    (h : ((@BetaStep Empty_set Γ ⊤)^*) t u)
  : nat
  := match h with
  | rtc_refl _ => 0
  | rtc_cons _ tail => S (unit_beta_length tail)
  end.

(** A duplicated argument follows two copies of its original path. The
    projections make the final result unit-typed for the length observation. *)

(** 被复制的实参分别沿原路径的两个副本归约；外层投影使最终结果为单位类型，
    便于观测路径长度。 *)

Definition duplicated_argument_path
  : ((@BetaStep Empty_set ∅ ⊤)^*)
      (π₁ ⟨unit_redex, unit_redex⟩) (π₁ ⟨⋆, ⋆⟩)
  := beta_rtc_lift op_fst
      (beta_rtc_single (⟨# var_zero, # var_zero⟩) unit_redex_path).

(** Duplication produces two steps from the supplied one-step path. *)

(** 复制将所给的单步路径变为两步路径。 *)

Example duplication_path_computes
  : unit_beta_length duplicated_argument_path = 2.
Proof. reflexivity. Qed.

(** An unused argument yields an empty path. *)

(** 未使用的实参给出空路径。 *)

Example discarded_argument_path_computes
  : unit_beta_length (beta_rtc_single (tm_unit : Tm (∅ ▻ ⊤) ⊤)
      unit_redex_path) = 0.
Proof. reflexivity. Qed.

(** A binder retains its fresh variable while the older assigned argument
    reduces. Apply to unit so that the result again admits length counting. *)

(** 旧赋值实参归约时，绑定保持其新变量。再应用于单位，使结果仍可计数长度。 *)

Definition under_binder_path
  : ((@BetaStep Empty_set ∅ ⊤)^*)
      ((ƛ (π₁ ⟨unit_redex⟨wkRen⟩, # var_zero⟩)) · ⋆)
      ((ƛ (π₁ ⟨⋆, # var_zero⟩)) · ⋆)
  := beta_rtc_lift (op_app_l ⋆)
      (beta_rtc_single
        (ƛ (π₁ ⟨# (var_succ var_zero), # var_zero⟩)) unit_redex_path).

(** Only the old assignment moves; the new binder contributes no step. *)

(** 只有旧赋值移动，新绑定不贡献步骤。 *)

Example binder_path_computes
  : unit_beta_length under_binder_path = 1.
Proof. reflexivity. Qed.

(** A renaming may identify the two unit variables, not just permute them. *)

(** 重命名可以识别两个单位变量，而不只是置换它们。 *)

Definition merge_unit_variables
  : Ren (∅ ▻ ⊤) (∅ ▻ ⊤ ▻ (⊤ : Ty Empty_set))
  := λ A x, match x with
  | inl (inl x) => match x with end
  | inl (inr x) => inr x
  | inr x => inr x
  end.

(** Two distinct open inputs become the same variable after renaming;
    the contraction still has exactly one contextual beta step. *)

(** 两个不同开放输入在重命名后成为同一变量，收缩仍恰含一个上下文 β 步骤。 *)

Definition identified_open_step
  : @BetaStep Empty_set (∅ ▻ ⊤) (⊤ × ⊤)
      (((ƛ (⟨# var_zero, # (var_succ (var_succ var_zero))⟩)) ·
        (# var_zero))⟨merge_unit_variables⟩)
      (⟨# var_zero, # var_zero⟩)
  := beta_step_rename
      (context_step_root _ (root_beta_function
        (⟨# var_zero, # (var_succ (var_succ var_zero))⟩) (# var_zero)))
      _ merge_unit_variables.

End Computations.
