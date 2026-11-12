From Cats Require Import
  STLC.Normalization
  STLC.EvaluationEquivalence
  STLC.Equivalence
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Universe Regressions for Semantic Substitution and Invariance *)

(** * 语义替换与不变性的宇宙回归检查 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_sub_scope.
Local Open Scope stlc_tm_scope.

(** ** Invariance with Small Equational Evidence

    Fix signature, contexts, terms and a substitution at [b < r < s < l].
    Check substitution compatibility and invariance with evidence at [b]. *)

(** ** 较小等式证据下的不变性

    在 [b < r < s < l] 处固定签名、上下文、项与替换，检查替换相容性及证据
    位于 [b] 时的不变性。 *)

Section SmallerEvidence.
Universes b r s l.
Constraint b < r.
Constraint r < s.
Constraint s < l.
Context (B : Type@{b}) (Γ Δ Θ : Ctx B) (A : Ty B)
    (t u : Tm Γ A) (σ : Sub Δ Γ).

(** Substitution maps retain the signature, world equality, semantic and
    world-law bounds of the public environment interface. *)

(** 替换映射保留公开环境接口的签名、世界相等、语义与世界定律界限。 *)

Definition separated_substitution
  : (EnvF Δ : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}) ⇒ EnvF Γ
  := EvalSubN Γ Δ σ.

(** The substitution lemma must work at these exact, distinct bounds. *)

(** 替换引理必须在这些指定且不同的界限处成立。 *)

Definition separated_substitution_law
    (γ : (EnvF Δ : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}) Θ)
  : eval t[σ] Θ γ ≈S eval t Θ (separated_substitution Θ γ)
  := eval_subst t Δ Θ σ γ.

(** Equality evidence may live at the signature level, strictly below
    semantic equality and the world-law bound. *)

(** 相等证据可位于签名层级，严格低于语义相等与世界定律界限。 *)

Definition smaller_evidence_evaluation (h : TmEq@{b b _} t u)
  : (EvalN t : (EnvF Γ :
      Functor ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}) ⇒ SemF A) ≈N EvalN u
  := eval_tm_eq h.

(** Invariance also retains the specified bounds hidden by its syntax-only
    result. The expected type fixes normalization's semantic instance. *)

(** 不变性也保留其纯语法结果中不可见的指定界限。预期类型固定正规化的语义
    实例。 *)

Definition smaller_evidence_invariance (h : TmEq@{b b _} t u)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t =
      nf@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u
  := nf_tm_eq h.

End SmallerEvidence.

(** ** Invariance with Larger Evidence

    Fix the same kinds of inputs at [b < r < l < s < e]. Check
    substitution and invariance with evidence above semantic values. *)

(** ** 较大证据下的不变性

    在 [b < r < l < s < e] 处固定同类输入，检查等式证据高于语义值时的替换
    与不变性。 *)

Section LargerEvidenceAndSmallerWorldLaws.
Universes b r l s e.
Constraint b < r.
Constraint r < l.
Constraint l < s.
Constraint s < e.
Context (B : Type@{b}) (Γ Δ Θ : Ctx B) (A : Ty B)
    (t u : Tm Γ A) (σ : Sub Δ Γ).

(** The semantic bound may exceed the world-law bound. *)

(** 语义界限可以高于世界定律界限。 *)

Definition smaller_law_substitution
  : (EnvF Δ : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}) ⇒ EnvF Γ
  := EvalSubN Γ Δ σ.

Definition smaller_law_substitution_law
    (γ : (EnvF Δ : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{s s _ _ _ _ _}) Θ)
  : eval t[σ] Θ γ ≈S eval t Θ (smaller_law_substitution Θ γ)
  := eval_subst t Δ Θ σ γ.

(** Evidence may in turn exceed semantic equality: eliminating a finite
    derivation adds no bound forcing it into the semantic universe. *)

(** 证据又可以高于语义相等：消去有限推导不会额外要求其容纳于语义宇宙。 *)

Definition larger_evidence_evaluation (h : TmEq@{b e _} t u)
  : (EvalN t : (EnvF Γ :
      Functor ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}) ⇒ SemF A) ≈N EvalN u
  := eval_tm_eq h.

Definition larger_evidence_invariance (h : TmEq@{b e _} t u)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t =
      nf@{b r s l
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u
  := nf_tm_eq h.

End LargerEvidenceAndSmallerWorldLaws.
