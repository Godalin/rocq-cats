From Cats.STLC Require Export
  ReductionRoot
  ReductionSource
  ReductionSubstitution.
From Cats.Set.Relation Require Import StrongNormalization.

(** * Reflecting Beta Steps through Renaming

    Renaming preserves the entire constructor tree, even when it identifies
    variables. Consequently each step of a renamed term comes from a step
    of the original term. This reflection, combined with preservation,
    transports strong normalization in both directions. It is specific to
    renaming: arbitrary substitution can create new redexes. *)

(** * 经重命名反射 β 步骤

    即使合并变量，重命名也保持整个构造器树。因此，重命名后项的每个步骤都
    来自原项的步骤。此反射结合保持性，双向传递强归一化。这是重命名特有的
    性质：任意替换可以产生新的可归约式。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Reconstructing Original Steps

    Fix syntax at [b], steps at [e] and an auxiliary classification bound
    [l]. Structural induction uses the source view to retain child steps;
    root observation handles a root contraction. Neither argument needs
    injective variable assignments or decidable base labels. *)

(** ** 重构原步骤

    固定 [b] 处的语法、[e] 处的步骤和辅助分类界 [l]。结构归纳用源视图保留
    子步骤；根观测处理根收缩。两者都不需要变量赋值单射或基标签可判定。 *)

Section RenameReflection.
Universes b e l.
Constraint b <= e, e < l.
Context {B : Type@{b}}.

(** Every renamed step has an original step with the same renamed target.
    The existential retains a computational step witness. *)

(** 每个重命名后的步骤都有原步骤，且目标的重命名相同；存在量词保留计算见证。 *)

Definition beta_step_rename_inv {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (ρ : Ren Δ Γ) (u : Tm Δ A),
      BetaStep@{b e l b} t⟨ρ⟩ u →
      ∃ v, BetaStep@{b e l b} t v ∧ u = v⟨ρ⟩.
Proof.
  induction t; intros Δ ρ u h.
  - exact (match beta_step_var_absurd _ h with end).
  - exact (match beta_step_unit_absurd h with end).
  - destruct (beta_step_pair_inv h) as [[v [k z]] | [v [k z]]].
    + destruct (IHt1 Δ ρ v k) as [w [p q]].
      exists ⟨w, t2⟩. split.
      * exact (beta_step_lift (op_pair_l t2) p).
      * cbn. now rewrite z, q.
    + destruct (IHt2 Δ ρ v k) as [w [p q]].
      exists ⟨t1, w⟩. split.
      * exact (beta_step_lift (op_pair_r t1) p).
      * cbn. now rewrite z, q.
  - destruct (beta_step_fst_inv h) as [r | [v [k z]]].
    + destruct (root_beta_rename_inv (π₁ t) Δ ρ r) as [v [p q]].
      exists v. split; [exact (context_step_root _ p) | exact q].
    + destruct (IHt Δ ρ v k) as [w [p q]].
      exists (π₁ w). split.
      * exact (beta_step_lift op_fst p).
      * cbn. now rewrite z, q.
  - destruct (beta_step_snd_inv h) as [r | [v [k z]]].
    + destruct (root_beta_rename_inv (π₂ t) Δ ρ r) as [v [p q]].
      exists v. split; [exact (context_step_root _ p) | exact q].
    + destruct (IHt Δ ρ v k) as [w [p q]].
      exists (π₂ w). split.
      * exact (beta_step_lift op_snd p).
      * cbn. now rewrite z, q.
  - destruct (beta_step_lam_inv h) as [v [k z]].
    destruct (IHt (Δ ▻ A) (ρ^↑Ren) v k) as [w [p q]].
    exists (ƛ w). split.
    + exact (beta_step_lift op_lam p).
    + cbn. now rewrite z, q.
  - destruct (beta_step_app_inv h) as [r | [[v [k z]] | [v [k z]]]].
    + destruct (root_beta_rename_inv (t1 · t2) Δ ρ r) as [v [p q]].
      exists v. split; [exact (context_step_root _ p) | exact q].
    + destruct (IHt1 Δ ρ v k) as [w [p q]].
      exists (w · t2). split.
      * exact (beta_step_lift (op_app_l t2) p).
      * cbn. now rewrite z, q.
    + destruct (IHt2 Δ ρ v k) as [w [p q]].
      exists (t1 · w). split.
      * exact (beta_step_lift (op_app_r t1) p).
      * cbn. now rewrite z, q.
Defined.

End RenameReflection.

(** ** Renaming Normalization Trees

    Keep the tree universe [s] independent of the step-classification
    universe [l], requiring only that [s] contains syntax and steps.
    Reflection recursively rebuilds all branches of the renamed tree;
    preservation pulls the tree back in the other direction. *)

(** ** 重命名归一化树

    树宇宙 [s] 与步骤分类宇宙 [l] 保持独立，只要求 [s] 容纳语法与步骤。
    反射递归重建重命名后树的全部分支；保持性将树沿反方向拉回。 *)

Section RenamedNormalization.
Universes b e s l.
Constraint b <= e, e <= s, e < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Strong normalization is preserved by every variable renaming. *)

(** 每个变量重命名都保持强归一化。 *)

Definition sn_beta_rename {t : Tm Γ A}
    (p : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t)
  : ∀ Δ (ρ : Ren Δ Γ), SN@{b e s} (@BetaStep@{b e l b} B Δ A) t⟨ρ⟩.
Proof.
  induction p as [t next ih]. intros Δ ρ. apply sn_intro.
  intros u h. destruct (beta_step_rename_inv t Δ ρ u h) as [v [k z]].
  subst u. exact (ih v k Δ ρ).
Defined.

(** Conversely, each original step is simulated by a renamed step. *)

(** 反方向上，每个原步骤都由重命名后的步骤模拟。 *)

Definition sn_beta_rename_inv (t : Tm Γ A) (Δ : Ctx B) (ρ : Ren Δ Γ)
    (p : SN@{b e s} (@BetaStep@{b e l b} B Δ A) t⟨ρ⟩)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := sn_simulation (λ u, u⟨ρ⟩)
      (λ u v h, beta_step_rename h Δ ρ) t p.

End RenamedNormalization.
