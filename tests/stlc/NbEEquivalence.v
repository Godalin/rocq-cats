From Cats Require Import
  STLC.Normalization
  STLC.EvaluationEquivalence
  STLC.Equivalence
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Universe Regressions for Semantic Substitution and Invariance *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_sub_scope.
Local Open Scope stlc_tm_scope.

(** ** Invariance with Small Equational Evidence

    Fix signature, contexts, terms and a substitution at [b < r < s < l].
    Check substitution compatibility and invariance with evidence at [b]. *)

Section SmallerEvidence.
Universes b r s l.
Constraint b < r.
Constraint r < s.
Constraint s < l.
Context (B : Type@{b}) (Γ Δ Θ : Ctx B) (A : Ty B)
    (t u : Tm Γ A) (σ : Sub Δ Γ).

(** Substitution maps retain the signature, world equality, semantic and
    world-law bounds of the public environment interface. *)

Definition separated_substitution
  : (EnvF Δ : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}) ⇒ EnvF Γ
  := EvalSubN Γ Δ σ.

(** The substitution lemma must work at these exact, distinct bounds. *)

Definition separated_substitution_law
    (γ : (EnvF Δ : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}) Θ)
  : eval t[σ] Θ γ ≈S eval t Θ (separated_substitution Θ γ)
  := eval_subst t Δ Θ σ γ.

(** Equality evidence may live at the signature level, strictly below
    semantic equality and the world-law bound. *)

Definition smaller_evidence_evaluation (h : TmEq@{b b _} t u)
  : (EvalN t : (EnvF Γ :
      Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}) ⇒ SemF A) ≈N EvalN u
  := eval_tm_eq h.

(** Invariance also retains the specified bounds hidden by its syntax-only
    result. The expected type fixes normalization's semantic instance. *)

Definition smaller_evidence_invariance (h : TmEq@{b b _} t u)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t =
      nf@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u
  := nf_tm_eq h.

End SmallerEvidence.

(** ** Invariance with Larger Evidence

    Fix the same kinds of inputs at [b < r < l < s < e]. Check
    substitution and invariance with evidence above semantic values. *)

Section LargerEvidenceAndSmallerWorldLaws.
Universes b r l s e.
Constraint b < r.
Constraint r < l.
Constraint l < s.
Constraint s < e.
Context (B : Type@{b}) (Γ Δ Θ : Ctx B) (A : Ty B)
    (t u : Tm Γ A) (σ : Sub Δ Γ).

(** The semantic bound may exceed the world-law bound. *)

Definition smaller_law_substitution
  : (EnvF Δ : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}) ⇒ EnvF Γ
  := EvalSubN Γ Δ σ.

Definition smaller_law_substitution_law
    (γ : (EnvF Δ : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}) Θ)
  : eval t[σ] Θ γ ≈S eval t Θ (smaller_law_substitution Θ γ)
  := eval_subst t Δ Θ σ γ.

(** Evidence may in turn exceed semantic equality: eliminating a finite
    derivation adds no bound forcing it into the semantic universe. *)

Definition larger_evidence_evaluation (h : TmEq@{b e _} t u)
  : (EvalN t : (EnvF Γ :
      Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}) ⇒ SemF A) ≈N EvalN u
  := eval_tm_eq h.

Definition larger_evidence_invariance (h : TmEq@{b e _} t u)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t =
      nf@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u
  := nf_tm_eq h.

End LargerEvidenceAndSmallerWorldLaws.
