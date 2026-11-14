From Cats.STLC Require Export
  PartialRenaming
  Reduction.
From Cats.Set.Relation Require Import Compatible.

(** * Contextual Steps under Partial Renaming

    A partial action need not be defined on every input. The appropriate
    preservation property therefore starts with a defined source and
    constructs a defined target together with its step. If root rules
    have this property, their full contextual closure has it too.
    The argument is independent of beta and eta. *)

(** * 部分重命名下的上下文步骤

    部分作用不必对每个输入有定义。因此适当的保持性质从一个有定义的来源
    出发，构造有定义的目标及其步骤。若根规则有此性质，其完整上下文闭包也
    有此性质。论证独立于 β 和 η。 *)

(** ** Restricting a Defined Source

    Fix arbitrary Type-valued root rules, with separate syntax, evidence
    and auxiliary classification bounds. Unchanged siblings must also
    have defined partial images; the source equation supplies them. *)

(** ** 限制有定义的来源

    固定任意 Type 值根规则，分离语法、证据及辅助分类界。未改变的兄弟项也
    必须有定义的部分像；来源方程提供这些像。 *)

Section PartialSteps.
Universes b e l.
Constraint b <= e, e < l.
Context {B : Type@{b}} (R : TmRelation@{b e l} B).

Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** Defined sources have defined targets related by a contextual step. *)

(** 有定义的来源具有由上下文步骤关联的有定义目标。 *)

Definition PartialStep {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : Type@{e}
  := ∀ (Δ : Ctx B) (σ : PartialRen Δ Γ) (t' : Tm Δ A),
      partial_rename t Δ σ = Some t' →
      ∃ u', partial_rename u Δ σ = Some u' ∧ ContextStep R t' u'.

(** Every one-hole constructor preserves this partial-action property. *)

(** 每个单孔构造器保持此部分作用性质。 *)

Definition partial_step_compatible
  : is_compatible (TmContexts B) (λ i, @PartialStep (fst i) (snd i)).
Proof.
  intros i j c x y ih.
  destruct c as [Γ A U q | Γ A U q | Γ A U | Γ A U |
    Γ A U | Γ A U q | Γ A U q]; intros Δ σ t' h;
    cbn in h.
  - change (match partial_rename x Δ σ, partial_rename q Δ σ with
      | Some a, Some d => Some (⟨a, d⟩) | _, _ => None end = Some t') in h.
    destruct (partial_rename x Δ σ) as [x' |] eqn:px;
      destruct (partial_rename q Δ σ) as [q' |] eqn:pq;
      try discriminate h.
    injection h as h. subst t'.
    destruct (ih Δ σ x' px) as [y' [py s]].
    exists (⟨y', q'⟩). split.
    + change (match partial_rename y Δ σ, partial_rename q Δ σ with
        | Some a, Some d => Some (⟨a, d⟩) | _, _ => None end =
        Some (⟨y', q'⟩)).
      rewrite py, pq. reflexivity.
    + exact (context_step_lift R (op_pair_l q') s).
  - change (match partial_rename q Δ σ, partial_rename x Δ σ with
      | Some a, Some d => Some (⟨a, d⟩) | _, _ => None end = Some t') in h.
    destruct (partial_rename q Δ σ) as [q' |] eqn:pq;
      destruct (partial_rename x Δ σ) as [x' |] eqn:px;
      try discriminate h.
    injection h as h. subst t'.
    destruct (ih Δ σ x' px) as [y' [py s]].
    exists (⟨q', y'⟩). split.
    + change (match partial_rename q Δ σ, partial_rename y Δ σ with
        | Some a, Some d => Some (⟨a, d⟩) | _, _ => None end =
        Some (⟨q', y'⟩)).
      rewrite pq, py. reflexivity.
    + exact (context_step_lift R (op_pair_r q') s).
  - change (option_map tm_fst (partial_rename x Δ σ) = Some t') in h.
    destruct (partial_rename x Δ σ) as [x' |] eqn:px;
      try discriminate h.
    injection h as h. subst t'.
    destruct (ih Δ σ x' px) as [y' [py s]].
    exists (tm_fst y'). split.
    + change (option_map tm_fst (partial_rename y Δ σ) = Some (tm_fst y')).
      rewrite py. reflexivity.
    + exact (context_step_lift R op_fst s).
  - change (option_map tm_snd (partial_rename x Δ σ) = Some t') in h.
    destruct (partial_rename x Δ σ) as [x' |] eqn:px;
      try discriminate h.
    injection h as h. subst t'.
    destruct (ih Δ σ x' px) as [y' [py s]].
    exists (tm_snd y'). split.
    + change (option_map tm_snd (partial_rename y Δ σ) = Some (tm_snd y')).
      rewrite py. reflexivity.
    + exact (context_step_lift R op_snd s).
  - change (option_map tm_lam
      (partial_rename x (Δ ▻ A) (partial_ren_lift σ)) = Some t') in h.
    destruct (partial_rename x (Δ ▻ A) (partial_ren_lift σ))
      as [x' |] eqn:px; try discriminate h.
    injection h as h. subst t'.
    destruct (ih (Δ ▻ A) (partial_ren_lift σ) x' px) as [y' [py s]].
    exists (ƛ y'). split.
    + change (option_map tm_lam
        (partial_rename y (Δ ▻ A) (partial_ren_lift σ)) = Some (ƛ y')).
      rewrite py. reflexivity.
    + exact (context_step_lift R op_lam s).
  - change (match partial_rename x Δ σ, partial_rename q Δ σ with
      | Some a, Some d => Some (a · d) | _, _ => None end = Some t') in h.
    destruct (partial_rename x Δ σ) as [x' |] eqn:px;
      destruct (partial_rename q Δ σ) as [q' |] eqn:pq;
      try discriminate h.
    injection h as h. subst t'.
    destruct (ih Δ σ x' px) as [y' [py s]].
    exists (y' · q'). split.
    + change (match partial_rename y Δ σ, partial_rename q Δ σ with
        | Some a, Some d => Some (a · d) | _, _ => None end =
        Some (y' · q')).
      rewrite py, pq. reflexivity.
    + exact (context_step_lift R (op_app_l q') s).
  - change (match partial_rename q Δ σ, partial_rename x Δ σ with
      | Some a, Some d => Some (a · d) | _, _ => None end = Some t') in h.
    destruct (partial_rename q Δ σ) as [q' |] eqn:pq;
      destruct (partial_rename x Δ σ) as [x' |] eqn:px;
      try discriminate h.
    injection h as h. subst t'.
    destruct (ih Δ σ x' px) as [y' [py s]].
    exists (q' · y'). split.
    + change (match partial_rename q Δ σ, partial_rename y Δ σ with
        | Some a, Some d => Some (a · d) | _, _ => None end =
        Some (q' · y')).
      rewrite pq, py. reflexivity.
    + exact (context_step_lift R (op_app_r q') s).
Defined.

(** Fold contextual derivations into their partial-image property. Root
    stability is the sole rule-specific input. *)

(** 将上下文推导折叠到其部分像性质；根稳定性是唯一依赖具体规则的输入。 *)

Definition context_step_partial
    (root_partial : ∀ Γ A (t u : Tm Γ A), R Γ A t u → PartialStep t u)
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : ContextStep R t u)
  : PartialStep t u
  := context_closure_preserves (TmContexts B) partial_step_compatible
      (λ i, root_partial (fst i) (snd i)) (Γ, A) t u h.

End PartialSteps.
