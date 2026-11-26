From Cats Require Import
  STLC.Normalization
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Executable NbE Interface Regressions *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** ** Evaluation at Separated Bounds

    Fix [B], [Γ], [A] and a term [t] with [b < r < s < l]. Check
    evaluation, initialization and normalization at these distinct bounds. *)

Section SeparatedBounds.
Universes b r s l.
Constraint b < r.
Constraint r < s.
Constraint s < l.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (t : Tm Γ A).

(** Evaluation retains distinct syntax, world equality, semantic and
    world-law bounds through its public natural-transformation interface. *)

Definition separated_evaluation
  : @Nat ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{s s _ _ _ _ _}
      (EnvF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ)
      (SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := EvalN t.

(** Initial environments use the same explicit semantic family. *)

Definition separated_initial_environment
  : EnvF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ Γ
  := initial_env Γ.

(** The complete executable pipeline and its renaming law retain these
    distinct bounds, including those hidden by the normal-syntax result. *)

Definition separated_normalization
  : Nf Γ A
  := nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t.

Definition separated_normalization_renaming (Δ : Ctx B) (ρ : Ren Δ Γ)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t⟨ρ⟩ =
      separated_normalization⟨ρ⟩nf.
Proof.
  exact (nf_rename@{b r s l
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t Δ ρ).
Defined.

(** Variable eta expansion also retains the chosen universe bounds. *)

Definition separated_variable_normalization (x : Var Γ A)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} (# x) =
      eta_expand_ne (ne_var x).
Proof.
  exact (nf_var@{b r s l
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} x).
Defined.

End SeparatedBounds.

(** ** Evaluation with Smaller World Laws

    Fix the same kinds of inputs with [b < r < l < s]. Check that
    evaluation and normalization also accept this order of bounds. *)

Section SmallerWorldLawBound.
Universes b r l s.
Constraint b < r.
Constraint r < l.
Constraint l < s.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (t : Tm Γ A).

(** Evaluation does not require semantic values to fit below world laws. *)

Definition smaller_world_law_evaluation
  : @Nat ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{s s _ _ _ _ _}
      (EnvF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ)
      (SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := EvalN t.

(** The normalization function also accepts this ordering of bounds. *)

Definition smaller_world_law_normalization
  : Nf Γ A
  := nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t.

Definition smaller_world_law_normalization_renaming
    (Δ : Ctx B) (ρ : Ren Δ Γ)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t⟨ρ⟩ =
      smaller_world_law_normalization⟨ρ⟩nf.
Proof.
  exact (nf_rename@{b r s l
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t Δ ρ).
Defined.

(** Variable eta expansion also retains the chosen universe bounds. *)

Definition smaller_world_law_variable_normalization (x : Var Γ A)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} (# x) =
      eta_expand_ne (ne_var x).
Proof.
  exact (nf_var@{b r s l
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} x).
Defined.

End SmallerWorldLawBound.

(** ** Executable Open-Term Normalization

    Fix arbitrary labels [p] and [q] and a context [Γ]. Check beta/eta
    normalization, capture avoidance and blocked higher-order applications. *)

Section Computations.
Context {B : Type} (p q : B) (Γ : Ctx B).

(** A beta redex at a base type computes to its open argument. *)

Example beta_identity_computes
  : nf ((ƛ (# var_zero)) · (# var_zero) : Tm (Γ ▻ ty_base p) _) =
      nf_base (ne_var var_zero).
Proof. reflexivity. Qed.

(** Evaluation reduces redexes inside an abstraction, not just at the
    outermost term node. *)

Example beta_under_lambda_computes
  : nf (ƛ ((ƛ (# var_zero)) · (# var_zero)) :
      Tm Γ (ty_base p ⇒ ty_base p)) =
      nf_lam (nf_base (ne_var var_zero)).
Proof. reflexivity. Qed.

(** Passing a free variable beneath another binder preserves its position
    relative to the new variable; it is not captured by that binder. *)

Example beta_avoids_capture
  : nf ((ƛ (ƛ (# (var_succ var_zero)))) · (# var_zero) :
      Tm (Γ ▻ ty_base p) (ty_base q ⇒ ty_base p)) =
      nf_lam (nf_base (ne_var (var_succ var_zero))).
Proof. reflexivity. Qed.

(** Pair construction and projection execute before reification. *)

Example product_beta_computes
  : nf (π₁ (⟨# var_zero, ⋆⟩) : Tm (Γ ▻ ty_base p) _) =
      nf_base (ne_var var_zero).
Proof. reflexivity. Qed.

(** Unit eta is enforced by the semantic singleton, including open inputs. *)

Example unit_eta_computes
  : nf (# var_zero : Tm (Γ ▻ ⊤) ⊤) = nf_unit.
Proof. reflexivity. Qed.

(** A free function becomes an eta-long lambda after normalization. *)

Example function_eta_computes
  : nf (# var_zero : Tm (Γ ▻ (ty_base p ⇒ ty_base q)) _) =
      nf_lam (nf_base (ne_app (ne_var (var_succ var_zero))
        (nf_base (ne_var var_zero)))).
Proof. reflexivity. Qed.

(** A blocked higher-order application reifies its function argument to
    an eta-long lambda, with both old variables weakened under its binder. *)

Example higher_order_open_application_computes
  : nf ((# var_zero) · (# (var_succ var_zero)) :
      Tm (Γ ▻ (ty_base p ⇒ ty_base q) ▻
        ((ty_base p ⇒ ty_base q) ⇒ ty_base q)) _) =
      nf_base (ne_app (ne_var var_zero)
        (nf_lam (nf_base
          (ne_app (ne_var (var_succ (var_succ var_zero)))
            (nf_base (ne_var var_zero)))))).
Proof. reflexivity. Qed.

(** A product variable expands by projections and type-directed eta. *)

Example product_eta_computes
  : nf (# var_zero : Tm (Γ ▻ (ty_base p × ⊤)) _) =
      nf_pair (nf_base (ne_fst (ne_var var_zero))) nf_unit.
Proof. reflexivity. Qed.

End Computations.
