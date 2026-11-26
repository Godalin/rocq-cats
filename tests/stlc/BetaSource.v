From Cats.STLC Require Import ReductionSource.
From Cats.Set.Relation Require Import Compatible.

(** * Beta Source-Analysis Regressions

    Check source views at separate and equal syntax/step levels, and
    neutral expansion with predicates both smaller and larger than step
    evidence. Concrete observations distinguish root, left/right child
    and binder cases in transparent derivations. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Separate Syntax and Step Universes

    Fix [b < e < l] with arbitrary base labels. Analysis and reconstruction
    keep step evidence at [e], while lambda inversion changes context. *)

Section SeparatedLevels.
Universes b e l.
Constraint b < e, e < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Analysis retains the larger step universe. *)

Definition separated_beta_source {t u : Tm Γ A}
    (h : BetaStep@{b e l b} t u)
  : BetaSource@{b e l} t u
  := beta_step_source h.

(** Reconstructing a source view also keeps that universe. *)

Definition separated_source_step {t u : Tm Γ A}
    (h : BetaSource@{b e l} t u)
  : BetaStep@{b e l b} t u
  := beta_source_step t u h.

(** Binder inversion returns a body in the extended context without label
    equality decisions or a fiber-injection assumption. *)

Definition separated_lambda_source {U : Ty B}
    {t : Tm (Γ ▻ A) U} {u : Tm Γ (A ⇒ U)}
    (h : BetaStep@{b e l b} (ƛ t) u)
  : ∃ t', BetaStep@{b e l b} t t' ∧ u = ƛ t'
  := beta_step_lam_inv h.

(** The hidden domain of an application is retained in its child cases. *)

Definition separated_application_source {U : Ty B}
    {f : Tm Γ (A ⇒ U)} {a : Tm Γ A} {u : Tm Γ U}
    (h : BetaStep@{b e l b} (f · a) u)
  : RootBeta@{b e b} (f · a) u ∨
    ((∃ f', BetaStep@{b e l b} f f' ∧ u = f' · a) ∨
     (∃ a', BetaStep@{b e l b} a a' ∧ u = f · a'))
  := beta_step_app_inv h.

End SeparatedLevels.

(** ** Equal Syntax and Step Universes

    Fix [b = e] and a larger classification bound. The source view does
    not require strict separation of syntax and actual step data. *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Both directions remain available at the common bound. *)

Definition equal_level_source_iff (t u : Tm Γ A)
  : BetaStep@{b b l b} t u ↔ BetaSource@{b b l} t u
  := beta_step_source_iff t u.

End EqualLevels.

(** ** Predicates Smaller than the Syntax

    Fix [p < b < e < l]. Expansion may return small data even though it
    inspects a larger step witness and its reconstructed target equation. *)

Section SmallerPredicate.
Universes p b e l.
Constraint p < b, b < e, e < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.
Context (P : Tm Γ A → Type@{p}).
Context (hp : ∀ t, is_neutral_tm t →
  (∀ u, BetaStep@{b e l b} t u → P u) → P t).

(** Application expansion imposes no lower bound on predicate data. *)

Definition smaller_predicate_application {U : Ty B}
    (f : Tm Γ (U ⇒ A)) (a : Tm Γ U)
    (hr : ∀ u, RootBeta@{b e b} (f · a) u → P u)
    (hf : ∀ f', BetaStep@{b e l b} f f' → P (f' · a))
    (ha : ∀ a', BetaStep@{b e l b} a a' → P (f · a'))
  : P (f · a)
  := neutral_expansion_app hp f a hr hf ha.

End SmallerPredicate.

(** ** Predicates Larger than the Classification Bound

    Reverse the order to [b < e < l < p]. The expansion law has its own
    auxiliary bound and does not force predicate data below [l]. *)

Section LargerPredicate.
Universes b e l p.
Constraint b < e, e < l, l < p.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.
Context (P : Tm Γ A → Type@{p}).
Context (hp : ∀ t, is_neutral_tm t →
  (∀ u, BetaStep@{b e l b} t u → P u) → P t).

(** Variable expansion returns the larger predicate witness directly. *)

Definition larger_predicate_variable (x : Var Γ A)
  : P (# x)
  := neutral_expansion_var hp x.

End LargerPredicate.

(** ** Observable Source Cases

    Use the empty base signature and unit/product/function types. Observe
    the branch selected by the constructed reduction, not an asserted
    uniqueness of all reductions from the same term. *)

Section Computations.

(** A closed unit redex and its original root-step witness. *)

Definition source_unit_redex
  : Tm (∅ : Ctx Empty_set) ⊤
  := (ƛ (# var_zero)) · ⋆.

(** Root witnesses embed into the existing contextual relation. *)

Definition source_unit_step
  : BetaStep source_unit_redex ⋆
  := context_step_root _ (root_beta_function (# var_zero) ⋆).

(** Observe which pair component changed. *)

Definition pair_source_tag {Γ : Ctx Empty_set} {A U : Ty Empty_set}
    {p : Tm Γ A} {q : Tm Γ U} {u : Tm Γ (A × U)}
    (h : BetaStep (⟨p, q⟩) u)
  : bool
  := match beta_step_pair_inv h with inl _ => false | inr _ => true end.

(** The left-child tag computes from the original closure witness. *)

Example pair_left_source_computes
  : pair_source_tag
      (context_step_lift _ (op_pair_l ⋆) source_unit_step) = false.
Proof. reflexivity. Qed.

(** Reconstructing a right-child source view preserves that tag. *)

Example pair_right_reconstruction_computes
  : pair_source_tag
      (beta_source_step (⟨⋆, source_unit_redex⟩) (⟨⋆, ⋆⟩)
        (inr (existT _ ⋆ (source_unit_step, eq_refl)))) = true.
Proof. reflexivity. Qed.

(** Observe root/function/argument alternatives by three distinct tags. *)

Definition app_source_tag {Γ : Ctx Empty_set} {A U : Ty Empty_set}
    {f : Tm Γ (A ⇒ U)} {a : Tm Γ A} {u : Tm Γ U}
    (h : BetaStep (f · a) u)
  : nat
  := match beta_step_app_inv h with
  | inl _ => 0
  | inr (inl _) => 1
  | inr (inr _) => 2
  end.

(** A function beta contraction selects the root alternative. *)

Example application_root_source_computes
  : app_source_tag source_unit_step = 0.
Proof. reflexivity. Qed.

(** The unit identity is also an argument of a higher-order redex. *)

Definition source_unit_identity
  : Tm (∅ : Ctx Empty_set) (⊤ ⇒ ⊤)
  := ƛ (# var_zero).

(** Reducing that higher-order function position keeps its own tag. *)

Example application_function_source_computes
  : app_source_tag (context_step_lift _ (op_app_l ⋆)
      (context_step_root _
        (root_beta_function (# var_zero) source_unit_identity))) = 1.
Proof. reflexivity. Qed.

(** An argument step is distinct from reducing the outer root redex. *)

Example application_argument_source_computes
  : app_source_tag (context_step_lift _ (op_app_r source_unit_identity)
      source_unit_step) = 2.
Proof. reflexivity. Qed.

(** A projection contraction exposes an actual root witness. *)

Example projection_root_source_computes
  : match beta_step_fst_inv
      (context_step_root _ (root_beta_fst
        (tm_unit : Tm (∅ : Ctx Empty_set) ⊤) ⋆)) with
    | inl _ => true
    | inr _ => false
    end = true.
Proof. reflexivity. Qed.

(** Reduction under second projection retains the reduced input as data. *)

Example projection_child_source_computes
  : match beta_step_snd_inv (context_step_lift _ op_snd
      (context_step_root _ (root_beta_function (# var_zero)
        (⟨tm_unit, tm_unit⟩ : Tm (∅ : Ctx Empty_set) (⊤ × ⊤))))) with
    | inl _ => false
    | inr _ => true
    end = true.
Proof. reflexivity. Qed.

(** Binder inversion returns the actual target body, preserving its scope. *)

Example lambda_body_source_computes
  : projT1 (beta_step_lam_inv (context_step_lift _ op_lam
      (context_step_root _ (root_beta_function (# var_zero)
        (# var_zero : Tm ((∅ : Ctx Empty_set) ▻ ⊤) ⊤))))) =
      (# var_zero).
Proof. reflexivity. Qed.

(** A raw beta redex is neutral here, even though it is not beta-normal. *)

Definition redex_is_raw_neutral
  : is_neutral_tm source_unit_redex
  := tt.

End Computations.
