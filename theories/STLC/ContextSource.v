From Cats.STLC Require Export ReductionPaths.
From Cats.Set.Relation Require Import Compatible.

(** * Source Analysis for Arbitrary Contextual Rules

    A contextual step either applies a root rule to the entire term or
    changes exactly one immediate child. This description is independent
    of the chosen root rules. It supports local-peak arguments for beta,
    eta and other rule families without injecting dependent constructors.
    Root rules remain possible at every source shape; specialized theories
    may subsequently rule out some of those alternatives. *)

(** * 任意上下文规则的源分析

    上下文步骤或者将根规则应用于整个项，或者恰好改变一个直接子项。此描述
    与所选根规则无关，可用于 β、η 及其他规则族的局部分叉论证，不需要对依赖
    构造器作单射消去。每种源形状都保留根规则的可能性，再由专化理论排除
    其中不可能的分支。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Root and Child Alternatives

    Fix arbitrary Type-valued root rules at every typing judgement.
    Child alternatives retain their contextual derivations and reconstruct
    the target with homogeneous syntax equality. Evidence and syntax have
    independent bounds, with the evidence bound containing the syntax. *)

(** ** 根与子项备选

    固定每个类型判断处的任意 Type 值根规则。子项分支保留上下文推导，并以
    同类型语法相等重构目标。证据界与语法界独立，前者容纳后者。 *)

Section ContextSources.
Universes b e l.
Constraint b <= e, e < l.
Context {B : Type@{b}} (R : TmRelation@{b e l} B).

(** The root alternative is uniform; child alternatives follow the actual
    typed source, preserving each hidden type and binder context. *)

(** 根分支一致给出；子项分支由实际带类型源项决定，保持隐藏类型及绑定上下文。 *)

Definition ContextSource {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : Type@{e}
  := R Γ A t u ∨
      match t in Tm Γ A return Tm Γ A → Type@{e} with
      | tm_var _ | tm_unit => λ _, Empty_set
      | tm_pair p q => λ v,
          (∃ p', ContextStep R p p' ∧ v = ⟨p', q⟩) ∨
          (∃ q', ContextStep R q q' ∧ v = ⟨p, q'⟩)
      | tm_fst p => λ v,
          ∃ p', ContextStep R p p' ∧ v = π₁ p'
      | tm_snd p => λ v,
          ∃ p', ContextStep R p p' ∧ v = π₂ p'
      | tm_lam p => λ v,
          ∃ p', ContextStep R p p' ∧ v = ƛ p'
      | tm_app f a => λ v,
          (∃ f', ContextStep R f f' ∧ v = f' · a) ∨
          (∃ a', ContextStep R a a' ∧ v = f · a')
      end u.

(** Keeping the step alongside its view supplies exactly the witness
    required when an enclosing constructor lifts the changed child. *)

(** 将步骤与视图一起保留，恰好提供外层构造器提升已改变子项时所需的见证。 *)

Definition context_source_compatible
  : is_compatible (TmContexts B)
      (λ i t u, ContextStep R t u ∧ ContextSource t u).
Proof.
  intros [Γ A] [Δ U] c t u [p q]. split.
  - exact (context_step_lift R c p).
  - right. destruct c; cbn.
    + exact (inl (existT _ u (p, eq_refl))).
    + exact (inr (existT _ u (p, eq_refl))).
    + exact (existT _ u (p, eq_refl)).
    + exact (existT _ u (p, eq_refl)).
    + exact (existT _ u (p, eq_refl)).
    + exact (inl (existT _ u (p, eq_refl))).
    + exact (inr (existT _ u (p, eq_refl))).
Defined.

(** Fold the original derivation; only its own root and context
    constructors are eliminated, with their indices generalized. *)

(** 折叠原推导；只在索引泛化后消去该推导自身的根与上下文构造器。 *)

Definition context_step_source {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : ContextStep R t u)
  : ContextSource t u
  := snd (context_closure_preserves (TmContexts B)
      context_source_compatible
      (λ i x y p, (context_step_root R p, inl p))
      (Γ, A) t u h).

(** Every view reconstructs a contextual step. The maps compare
    presentations of the relation, not equality of derivations. *)

(** 每个视图重构一个上下文步骤。两个映射比较关系的呈现，不比较推导相等。 *)

Definition context_source_step {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : ContextSource t u → ContextStep R t u.
Proof.
  intros [h | h]; [exact (context_step_root R h) |].
  destruct t; cbn in h.
  - destruct h.
  - destruct h.
  - destruct h as [[v [h z]] | [v [h z]]]; subst u.
    + exact (context_step_lift R (op_pair_l t2) h).
    + exact (context_step_lift R (op_pair_r t1) h).
  - destruct h as [v [h z]]. subst u.
    exact (context_step_lift R op_fst h).
  - destruct h as [v [h z]]. subst u.
    exact (context_step_lift R op_snd h).
  - destruct h as [v [h z]]. subst u.
    exact (context_step_lift R op_lam h).
  - destruct h as [[v [h z]] | [v [h z]]]; subst u.
    + exact (context_step_lift R (op_app_l t2) h).
    + exact (context_step_lift R (op_app_r t1) h).
Defined.

End ContextSources.
