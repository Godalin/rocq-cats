From Cats.STLC Require Import StrongNormalization.

(** * STLC Strong-Normalization Regressions

    Check independent candidate membership, path, tree and law bounds;
    all-term normalization at separated and equal levels; and the binder
    premise of the substitution theorem. Examples include duplication,
    discarding, higher-order use and reductions under a lambda. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Paths below Normalization Trees

    Fix [p < a < r < w < s < k]. A path at [w] transports membership at
    the smaller [p], independently of the candidate's tree bound [s]. *)

Section SmallerPaths.
Universes p a r w s k.
Constraint p < a, a < r, r < w, w < s, s < k.
Context {X : Type@{a}} (R : X → X → Type@{r}) (N : X → Set).
Context (P : X → Type@{p}).
Context (hP : IsReducibilityCandidate@{a r Set p s k} R N P).

(** Small paths need not share the normalization-tree size. *)

Definition smaller_path_membership {x y : X}
    (h : ReflTransClos@{a r w} R x y)
  : P x → P y
  := candidate_rtc hP h.

End SmallerPaths.

(** ** Paths above Candidate Laws

    Fix [r < a < s < p < k < w]. Large path evidence may transport large
    membership while candidate trees and laws remain smaller than the path. *)

Section LargerPaths.
Universes r a s p k w.
Constraint r < a, a < s, s < p, p < k, k < w.
Context {X : Type@{a}} (R : X → X → Type@{r}) (N : X → Set).
Context (P : X → Type@{p}).
Context (hP : IsReducibilityCandidate@{a r Set p s k} R N P).

(** No path-to-tree or path-to-law resizing is assumed. *)

Definition larger_path_membership {x y : X}
    (h : ReflTransClos@{a r w} R x y)
  : P x → P y
  := candidate_rtc hP h.

End LargerPaths.

(** ** Candidate Expansion with Small Membership

    Fix [p < b < e < s < k < l]. Candidate laws may lie below relation
    classification while expansion returns smaller membership data. *)

Section SmallCandidate.
Universes p b e s k l.
Constraint p < b, b < e, e < s, s < k, k < l.
Context {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}.
Context (P : Tm Γ U → Type@{p}).
Context (hP : IsReducibilityCandidate@{b e Set p s k}
  (@BetaStep@{b e l b} B Γ U) (@is_neutral_tm B Γ U) P).

(** Function beta expansion retains the independent candidate bounds. *)

Definition small_candidate_beta (t : Tm (Γ ▻ A) U) (u : Tm Γ A)
    (hu : SN@{b e s} (@BetaStep@{b e l b} B Γ A) u) (ht : P t[u/])
  : P ((ƛ t) · u)
  := candidate_beta_function P hP t u hu ht.

(** A projection may discard a component whose evidence is much larger
    than the selected component's membership. *)

Definition small_candidate_projection (t : Tm Γ U) (u : Tm Γ A)
    (ht : P t) (hu : SN@{b e s} (@BetaStep@{b e l b} B Γ A) u)
  : P (π₁ ⟨t, u⟩)
  := candidate_fst_pair P hP t u ht hu.

End SmallCandidate.

(** ** Candidate Expansion with Large Membership

    Fix [b < e < l < s < p < k]. Membership may exceed the tree universe
    and the relation-classification bound in the expansion theorem. *)

Section LargeCandidate.
Universes b e l s p k.
Constraint b < e, e < l, l < s, s < p, p < k.
Context {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}.
Context (P : Tm Γ U → Type@{p}).
Context (hP : IsReducibilityCandidate@{b e Set p s k}
  (@BetaStep@{b e l b} B Γ U) (@is_neutral_tm B Γ U) P).

(** The beta result is allowed to carry data larger than its SN trees. *)

Definition large_candidate_beta (t : Tm (Γ ▻ A) U) (u : Tm Γ A)
    (hu : SN@{b e s} (@BetaStep@{b e l b} B Γ A) u) (ht : P t[u/])
  : P ((ƛ t) · u)
  := candidate_beta_function P hP t u hu ht.

(** The other projection keeps the same independent bounds. *)

Definition large_candidate_projection (t : Tm Γ A) (u : Tm Γ U)
    (ht : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t) (hu : P u)
  : P (π₂ ⟨t, u⟩)
  := candidate_snd_pair P hP t u ht hu.

End LargeCandidate.

(** ** All Terms at Separate Levels

    Fix [b < e < s < l] and arbitrary labels. The main theorem gives a
    normalization tree with the requested step/tree sizes. The fundamental
    theorem handles arbitrary reducible assignments and future binders. *)

Section SeparatedLevels.
Universes b e s l.
Constraint b < e, e < s, s < l.
Context {B : Type@{b}} {Γ Δ : Ctx B} {A : Ty B}.

(** No hypothesis of reducibility remains in the final theorem. *)

Definition separated_beta_sn (t : Tm Γ A)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := beta_strong_normalization t.

(** The substitution theorem retains the declared membership universe. *)

Definition separated_substitution (t : Tm Γ A) (σ : Sub Δ Γ)
    (h : is_reducible_sub@{b e s l} σ)
  : Reducible@{b e s l} A Δ t[σ]
  := reducible_subst t Δ σ h.

(** The binder test assigns old variables after renaming and the newest
    one directly, using only the explicit reducibility hypotheses. *)

Definition separated_binder {U : Ty B} (t : Tm (Γ ▻ A) U)
    (σ : Sub Δ Γ) (h : is_reducible_sub@{b e s l} σ)
  : Reducible@{b e s l} (A ⇒ U) Δ (ƛ t[σ^↑Sub])
  := reducible_subst (ƛ t) Δ σ h.

End SeparatedLevels.

(** ** Large Trees above Classification

    Fix [b < e < l < s]. Strong normalization does not force its tree
    universe below the relation-classification universe. *)

Section LargeTrees.
Universes b e l s.
Constraint b < e, e < l, l < s.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** All terms normalize at a tree bound larger than classification. *)

Definition large_tree_beta_sn (t : Tm Γ A)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := beta_strong_normalization t.

End LargeTrees.

(** ** Equal Computational Levels

    Fix syntax, step and tree universes equal to [b], with only [b < l]
    for classification. No strict separation of actual witnesses is needed. *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The theorem is also available at a common computational bound. *)

Definition equal_level_beta_sn (t : Tm Γ A)
  : SN@{b b b} (@BetaStep@{b b l b} B Γ A) t
  := beta_strong_normalization t.

End EqualLevels.

(** ** Duplication, Discarding and Binders

    Use an empty base signature. The examples expose beta steps in
    arguments even when the root would discard them, duplication into
    products, higher-order application and full reduction under a lambda.
    All receive SN trees from the same unconditional theorem. *)

Section Examples.

(** A closed unit redex used as an argument. *)

Definition unit_redex
  : Tm (@ctx_empty Empty_set) ⊤
  := (ƛ (# var_zero)) · ⋆.

(** Duplication substitutes the argument into both pair components. *)

Definition duplicating_redex
  : Tm (@ctx_empty Empty_set) (⊤ × ⊤)
  := (ƛ (⟨# var_zero, # var_zero⟩)) · unit_redex.

(** The unused argument can still reduce before the root contraction. *)

Definition discarding_redex
  : Tm (@ctx_empty Empty_set) ⊤
  := (ƛ ⋆) · unit_redex.

(** A higher-order identity applied to an identity and then unit. *)

Definition higher_order_redex
  : Tm (@ctx_empty Empty_set) ⊤
  := ((ƛ (# var_zero)) · (ƛ (# var_zero))) · ⋆.

(** A beta step remains possible under an unapplied lambda. *)

Definition binder_redex
  : Tm (@ctx_empty Empty_set) (⊤ ⇒ ⊤)
  := ƛ ((ƛ (# var_zero)) · (# var_zero)).

(** Duplication has a normalization tree, without selecting a strategy. *)

Example duplication_sn
  : SN BetaStep duplicating_redex
  := beta_strong_normalization duplicating_redex.

(** Discarding also covers the argument-first reduction choice. *)

Example discarding_argument_sn
  : SN BetaStep ((ƛ ⋆) · (⋆ : Tm (@ctx_empty Empty_set) ⊤))
  := sn_step (beta_strong_normalization discarding_redex)
      (beta_step_lift (op_app_r (ƛ ⋆))
        (context_step_root _ (root_beta_function (# var_zero) ⋆))).

(** Higher-order application is covered by the same all-terms theorem. *)

Example higher_order_sn
  : SN BetaStep higher_order_redex
  := beta_strong_normalization higher_order_redex.

(** Follow the body step under the lambda, preserving an SN subtree. *)

Example binder_reduct_sn
  : SN BetaStep (ƛ (# var_zero) : Tm (@ctx_empty Empty_set) (⊤ ⇒ ⊤))
  := sn_step (beta_strong_normalization binder_redex)
      (beta_step_lift op_lam
        (context_step_root _
          (root_beta_function (# var_zero) (# var_zero)))).

(** An infinite sequence would contradict the theorem's tree. *)

Example no_closed_unit_infinite_sequence
    (f : nat → Tm (@ctx_empty Empty_set) ⊤)
  : (∀ n, BetaStep (f n) (f (S n))) → Empty_set
  := beta_no_infinite_sequence f.

End Examples.
