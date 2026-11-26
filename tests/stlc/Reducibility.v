From Cats.STLC Require Import Reducibility.

(** * Reducibility Interface Regressions

    Check independent candidate universes, normalization trees on both
    sides of the step-classification bound, equal-level use, noninjective
    renaming and transparent root observations. These examples do not
    assert reducibility of all typed terms. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Small Membership and Larger Edge Evidence

    Fix [p < a < r < s < k], with neutrality at an independent [n < k].
    Small membership can entail a larger normalization tree without
    shrinking the stored step witnesses. *)

Section SmallMembership.
Universes p a r n s k.
Constraint p < a, a < r, r < s, s < k, n < k.
Context {X : Type@{a}} (R : X → X → Type@{r}).
Context (N : X → Type@{n}) (P Q : X → Type@{p}).
Context (h : IsReducibilityCandidate@{a r n p s k} R N P).

(** The general interface preserves a separate tree universe. *)

Definition small_membership_sn (x : X) (p : P x)
  : SN@{a r s} R x
  := @candidate_sn _ R N P h x p.

(** Pointwise equivalence transports all laws, retaining the same bounds. *)

Definition small_membership_equiv (e : ∀ x, P x ↔ Q x)
  : IsReducibilityCandidate@{a r n p s k} R N Q
  := fst (IsReducibilityCandidate_proper R N P Q e) h.

End SmallMembership.

(** ** Large Membership and Smaller Edge Evidence

    Fix [n < r < a < s < p < k]. A candidate may store large membership
    data while returning a smaller normalization tree. This does not
    resize its members: its normalization law is an explicit assumption. *)

Section LargeMembership.
Universes n r a s p k.
Constraint n < r, r < a, a < s, s < p, p < k.
Context {X : Type@{a}} (R : X → X → Type@{r}).
Context (N : X → Type@{n}) (P : X → Type@{p}).
Context (h : IsReducibilityCandidate@{a r n p s k} R N P).

(** Membership and normalization evidence need not share a universe. *)

Definition large_membership_sn (x : X) (p : P x)
  : SN@{a r s} R x
  := @candidate_sn _ R N P h x p.

End LargeMembership.

(** ** Trees below the Classification Bound

    Fix [b < e < s < l] and arbitrary labels. Reducibility supports
    normalization, neutral expansion, step closure and reindexing without
    a label equality decision. *)

Section SmallerTrees.
Universes b e s l.
Constraint b < e, e < s, s < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** A reducible term returns the declared normalization tree. *)

Definition smaller_tree_sn (t : Tm Γ A) (p : Reducible@{b e s l} A Γ t)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := reducible_sn A Γ t p.

(** All reducts suffice for a neutral source, at the same independent levels. *)

Definition smaller_tree_expand (t : Tm Γ A) (n : is_neutral_tm t)
    (h : ∀ u, BetaStep@{b e l b} t u → Reducible@{b e s l} A Γ u)
  : Reducible@{b e s l} A Γ t
  := reducible_expand A Γ t n h.

(** Renaming changes the context, including variable-identifying maps. *)

Definition smaller_tree_rename (t : Tm Γ A)
    (p : Reducible@{b e s l} A Γ t) (Δ : Ctx B) (ρ : Ren Δ Γ)
  : Reducible@{b e s l} A Δ t⟨ρ⟩
  := reducible_rename A Γ t p Δ ρ.

(** A step preserves reducibility without changing its witness universe. *)

Definition smaller_tree_step (t u : Tm Γ A)
    (h : BetaStep@{b e l b} t u) (p : Reducible@{b e s l} A Γ t)
  : Reducible@{b e s l} A Γ u
  := reducible_step A Γ t u h p.

(** Reflection retains the larger step universe when rebuilding a target. *)

Definition smaller_tree_reflect (t : Tm Γ A) (Δ : Ctx B) (ρ : Ren Δ Γ)
    (u : Tm Δ A) (h : BetaStep@{b e l b} t⟨ρ⟩ u)
  : ∃ v, BetaStep@{b e l b} t v ∧ u = v⟨ρ⟩
  := beta_step_rename_inv t Δ ρ u h.

End SmallerTrees.

(** ** Trees above the Classification Bound

    Fix [b < e < l < s]. The relation-classification universe does not
    bound the stored reducibility or normalization witnesses. *)

Section LargerTrees.
Universes b e l s.
Constraint b < e, e < l, l < s.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** A variable is reducible at a bound above relation classification. *)

Definition larger_tree_var (x : Var Γ A)
  : Reducible@{b e s l} A Γ (# x)
  := reducible_var A Γ x.

(** Function reducibility is tested in a genuinely extended context. *)

Definition larger_tree_function_test {U : Ty B} (f : Tm Γ (A ⇒ U))
    (p : Reducible@{b e s l} (A ⇒ U) Γ f)
  : Reducible@{b e s l} U (Γ ▻ A) (f⟨wkRen⟩ · (# var_zero))
  := p (Γ ▻ A) wkRen (# var_zero) (reducible_var A (Γ ▻ A) var_zero).

(** The candidate instance uses the same large tree universe. *)

Definition larger_tree_candidate (t : Tm Γ A)
    (p : Reducible@{b e s l} A Γ t)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := @candidate_sn _ _ _ _ (Reducible_IsReducibilityCandidate A Γ) t p.

End LargerTrees.

(** ** Equal Syntax, Step and Tree Universes

    Fix one common [b] and a larger [l]. The theory does not require
    strict separation among the actual computational witnesses. *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Every variable yields an equal-level normalization tree. *)

Definition equal_level_variable_sn (x : Var Γ A)
  : SN@{b b b} (@BetaStep@{b b l b} B Γ A) (# x)
  := reducible_sn A Γ (# x) (reducible_var A Γ x).

End EqualLevels.

(** ** Independent Root-Witness Sizes

    Fix [b < r < s]. Uniqueness compares targets of root derivations
    whose edge witnesses live at different levels, in either argument order. *)

Section RootSizes.
Universes b r s.
Constraint b < r, r < s.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B} {t u v : Tm Γ A}.

(** Small then large root evidence. *)

Definition root_unique_small_large (h : RootBeta@{b r b} t u)
    (k : RootBeta@{b s b} t v)
  : u = v
  := root_beta_unique h k.

(** Large then small root evidence. *)

Definition root_unique_large_small (h : RootBeta@{b s b} t u)
    (k : RootBeta@{b r b} t v)
  : u = v
  := root_beta_unique h k.

End RootSizes.

(** ** Transparent Computations

    Use an empty base signature and two unit variables. A renaming
    identifies both variables; reflection must still recover the original
    beta target. Root observation must not search inside constructors. *)

Section Computations.

(** A two-variable context and a one-variable destination. *)

Definition two_units
  : Ctx Empty_set
  := (∅ ▻ ⊤) ▻ ⊤.

(** Both old variables are assigned the same destination variable. *)

Definition identify_units
  : Ren (∅ ▻ ⊤) two_units.
Proof.
  intros A [x | x].
  - destruct x as [x | x]; [destruct x | destruct x; exact var_zero].
  - destruct x. exact var_zero.
Defined.

(** The argument deliberately selects the older source variable. *)

Definition identifying_redex
  : Tm two_units ⊤
  := (ƛ (# var_zero)) · (# (var_succ var_zero)).

(** Observation computes the single root beta contractum. *)

Example root_function_computes
  : root_contractum identifying_redex = Some (# (var_succ var_zero)).
Proof. reflexivity. Defined.

(** Reflection recovers the older variable even though its image agrees
    with the newer variable's image. No injectivity assumption is hidden. *)

Example identifying_reflection_computes
  : projT1 (beta_step_rename_inv identifying_redex (∅ ▻ ⊤)
      identify_units (# var_zero)
      (context_step_root _ (root_beta_function (# var_zero) (# var_zero))))
      = (# (var_succ var_zero)).
Proof. reflexivity. Defined.

(** Reflection also lifts under a binder, keeping its fresh variable
    separate from the identified older variables. *)

Example binder_reflection_computes
  : projT1 (beta_step_rename_inv
      (ƛ ((ƛ (# var_zero)) · (# (var_succ var_zero)))
        : Tm two_units (⊤ ⇒ ⊤))
      (∅ ▻ ⊤) identify_units (ƛ (# (var_succ var_zero)))
      (beta_step_lift op_lam
        (context_step_root _
          (root_beta_function (# var_zero) (# (var_succ var_zero))))))
      = (ƛ (# (var_succ var_zero))).
Proof. reflexivity. Defined.

(** Projection observes the first component directly. *)

Example root_projection_computes
  : root_contractum (π₁ ⟨identifying_redex, (⋆ : Tm two_units ⊤)⟩)
      = Some identifying_redex.
Proof. reflexivity. Defined.

(** A redex underneath a pair is not a root contraction of that pair. *)

Example root_pair_does_not_search
  : root_contractum (⟨identifying_redex, (⋆ : Tm two_units ⊤)⟩) = None.
Proof. reflexivity. Defined.

End Computations.
