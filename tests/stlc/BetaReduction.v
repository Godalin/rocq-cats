From Cats.STLC Require Import ReductionSubstitution.
From Cats.Set.Relation Require Import Compatible.

(** * Directed Beta Interface Regressions

    Check the generic substitution fold at unequal source/target witness
    levels and beta preservation at distinct and equal syntax/step levels.
    Concrete paths exercise duplication, discarded inputs, binding and
    variable identification, without a decision procedure for type labels. *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Larger Target Witnesses

    Fix [b < r < s], arbitrary root systems and a substituted-generator
    interpreter. The context fold must preserve these distinct sizes. *)

Section LargerTarget.
Universes b r s.
Constraint b < r, r < s.
Context {B : Type@{b}}.
Context (R : TmRelation@{b r _} B) (S : TmRelation@{b s _} B).
Context (hr : ∀ Γ A (t u : Tm Γ A), R Γ A t u →
  ∀ Δ (σ : Sub Δ Γ), ContextStep S t[σ] u[σ]).

(** Generic contextual preservation accepts strictly larger target edges. *)

Definition context_subst_larger_target {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : ContextStep R t u)
    (Δ : Ctx B) (σ : Sub Δ Γ)
  : ContextStep S t[σ] u[σ]
  := context_step_subst R S hr h Δ σ.

End LargerTarget.

(** ** Smaller Target Witnesses

    Reverse the edge-size order to [b < s < r]. The fold transforms given
    source evidence; it need not retain that evidence in the target. *)

Section SmallerTarget.
Universes b r s.
Constraint b < s, s < r.
Context {B : Type@{b}}.
Context (R : TmRelation@{b r _} B) (S : TmRelation@{b s _} B).
Context (hr : ∀ Γ A (t u : Tm Γ A), R Γ A t u →
  ∀ Δ (σ : Sub Δ Γ), ContextStep S t[σ] u[σ]).

(** No spurious source-to-target universe bound is imposed. *)

Definition context_subst_smaller_target {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : ContextStep R t u)
    (Δ : Ctx B) (σ : Sub Δ Γ)
  : ContextStep S t[σ] u[σ]
  := context_step_subst R S hr h Δ σ.

End SmallerTarget.

(** ** Beta Evidence above Syntax

    Fix [b < e < p] and arbitrary base labels. Check large beta evidence,
    a still larger path bound, and pointwise assignment reduction. *)

Section SeparatedLevels.
Universes b e p.
Constraint b < e, e < p.
Context {B : Type@{b}} {Γ Δ : Ctx B} {A : Ty B}.

(** Root substitution keeps the larger evidence bound. *)

Definition separated_root_subst {t u : Tm Γ A}
    (h : RootBeta@{b e _} t u) (σ : Sub Δ Γ)
  : RootBeta@{b e _} t[σ] u[σ]
  := root_beta_subst h Δ σ.

(** The same check for full contexts includes non-root occurrences. *)

Definition separated_step_subst {t u : Tm Γ A}
    (h : BetaStep@{b e _ _} t u) (σ : Sub Δ Γ)
  : BetaStep@{b e _ _} t[σ] u[σ]
  := beta_step_subst h Δ σ.

(** Renaming does not collapse the edge universe to syntax. *)

Definition separated_step_rename {t u : Tm Γ A}
    (h : BetaStep@{b e _ _} t u) (ρ : Ren Δ Γ)
  : BetaStep@{b e _ _} t⟨ρ⟩ u⟨ρ⟩
  := beta_step_rename h Δ ρ.

(** Path substitution keeps a bound strictly above the individual edges. *)

Definition separated_path_subst {t u : Tm Γ A}
    (h : ReflTransClos@{b e p} (@BetaStep@{b e _ _} B Γ A) t u)
    (σ : Sub Δ Γ)
  : ReflTransClos@{b e p} (@BetaStep@{b e _ _} B Δ A) t[σ] u[σ]
  := beta_rtc_subst h Δ σ.

(** The generic one-hole lift can change context and result type. *)

Definition separated_path_lift {U : Ty B}
    (c : TmOperation (Γ, A) (Δ, U)) {t u : Tm Γ A}
    (h : ReflTransClos@{b e p} (@BetaStep@{b e _ _} B Γ A) t u)
  : ReflTransClos@{b e p} (@BetaStep@{b e _ _} B Δ U)
      (TmContexts B (Γ, A) (Δ, U) c t)
      (TmContexts B (Γ, A) (Δ, U) c u)
  := beta_rtc_lift c h.

(** Assignment reduction also accepts beta evidence above syntax. *)

Definition separated_assignment_path (t : Tm Γ A) (σ τ : Sub Δ Γ)
    (h : ∀ U x, ReflTransClos@{b e p}
      (@BetaStep@{b e _ _} B Δ U) (σ U x) (τ U x))
  : ReflTransClos@{b e p} (@BetaStep@{b e _ _} B Δ A) t[σ] t[τ]
  := subst_beta_rtc t Δ σ τ h.

(** Both a term path and its assignment paths can use the larger bound. *)

Definition separated_both_path {t u : Tm Γ A}
    (h : ReflTransClos@{b e p} (@BetaStep@{b e _ _} B Γ A) t u)
    {σ τ : Sub Δ Γ}
    (k : ∀ U x, ReflTransClos@{b e p}
      (@BetaStep@{b e _ _} B Δ U) (σ U x) (τ U x))
  : ReflTransClos@{b e p} (@BetaStep@{b e _ _} B Δ A) t[σ] u[τ]
  := beta_rtc_subst_both h k.

(** Single-variable replacement also retains the larger path universe. *)

Definition separated_single_path {U : Ty B} (t : Tm (Γ ▻ A) U)
    {u v : Tm Γ A}
    (h : ReflTransClos@{b e p} (@BetaStep@{b e _ _} B Γ A) u v)
  : ReflTransClos@{b e p} (@BetaStep@{b e _ _} B Γ U) t[u/] t[v/]
  := beta_rtc_single t h.

End SeparatedLevels.

(** ** Equal Syntax and Evidence Levels

    Fix an arbitrary signature at one common level; strict separation is
    not required by the interface. *)

Section EqualLevels.
Universe b.
Context {B : Type@{b}} {Γ Δ : Ctx B} {A : Ty B}.

(** Full-step preservation permits the equal-level instance. *)

Definition equal_level_step_subst {t u : Tm Γ A}
    (h : BetaStep@{b b _ _} t u) (σ : Sub Δ Γ)
  : BetaStep@{b b _ _} t[σ] u[σ]
  := beta_step_subst h Δ σ.

End EqualLevels.

(** ** Concrete Directed Paths

    Work over the empty base signature, using unit and function/product
    types. Measure the number of contextual beta edges, not the size of
    their evidence or the length of an equational conversion. *)

Section Computations.

(** A closed beta redex with unit result. *)

Definition unit_redex
  : Tm (∅ : Ctx Empty_set) ⊤
  := (ƛ (# var_zero)) · ⋆.

(** Its contraction supplies a one-edge directed path. *)

Definition unit_redex_path
  : ((@BetaStep Empty_set ∅ ⊤)^*) unit_redex ⋆
  := rtc_step (context_step_root _ (root_beta_function (# var_zero) ⋆)).

(** This test observation counts edges in a unit-typed beta path. *)

Fixpoint unit_beta_length {Γ : Ctx Empty_set} {t u : Tm Γ ⊤}
    (h : ((@BetaStep Empty_set Γ ⊤)^*) t u)
  : nat
  := match h with
  | rtc_refl _ => 0
  | rtc_cons _ tail => S (unit_beta_length tail)
  end.

(** A duplicated argument follows two copies of its original path. The
    projections make the final result unit-typed for the length observation. *)

Definition duplicated_argument_path
  : ((@BetaStep Empty_set ∅ ⊤)^*)
      (π₁ ⟨unit_redex, unit_redex⟩) (π₁ ⟨⋆, ⋆⟩)
  := beta_rtc_lift op_fst
      (beta_rtc_single (⟨# var_zero, # var_zero⟩) unit_redex_path).

(** Duplication produces two steps from the supplied one-step path. *)

Example duplication_path_computes
  : unit_beta_length duplicated_argument_path = 2.
Proof. reflexivity. Qed.

(** An unused argument yields an empty path. *)

Example discarded_argument_path_computes
  : unit_beta_length (beta_rtc_single (tm_unit : Tm (∅ ▻ ⊤) ⊤)
      unit_redex_path) = 0.
Proof. reflexivity. Qed.

(** A binder retains its fresh variable while the older assigned argument
    reduces. Apply to unit so that the result again admits length counting. *)

Definition under_binder_path
  : ((@BetaStep Empty_set ∅ ⊤)^*)
      ((ƛ (π₁ ⟨unit_redex⟨wkRen⟩, # var_zero⟩)) · ⋆)
      ((ƛ (π₁ ⟨⋆, # var_zero⟩)) · ⋆)
  := beta_rtc_lift (op_app_l ⋆)
      (beta_rtc_single
        (ƛ (π₁ ⟨# (var_succ var_zero), # var_zero⟩)) unit_redex_path).

(** Only the old assignment moves; the new binder contributes no step. *)

Example binder_path_computes
  : unit_beta_length under_binder_path = 1.
Proof. reflexivity. Qed.

(** A renaming may identify the two unit variables, not just permute them. *)

Definition merge_unit_variables
  : Ren (∅ ▻ ⊤) (∅ ▻ ⊤ ▻ (⊤ : Ty Empty_set))
  := λ A x, match x with
  | inl (inl x) => match x with end
  | inl (inr x) => inr x
  | inr x => inr x
  end.

(** Two distinct open inputs become the same variable after renaming;
    the contraction still has exactly one contextual beta step. *)

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
