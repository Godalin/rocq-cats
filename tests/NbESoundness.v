From Cats Require Import
  STLC.Normalization
  STLC.LogicalRelation
  STLC.Equivalence.

(** * Universe Regressions for Normalization Soundness *)

(** * 正规化可靠性的宇宙回归检查 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

Section SmallerEvidence.
Universes b r s l.
Constraint b < r.
Constraint r < s.
Constraint s < l.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B).

(** Fix the semantic instance hidden by normalization's syntax result.
    Long universe instances are confined to these boundary regressions. *)

(** 固定正规化语法结果中不可见的语义实例。长宇宙实例只用于这些边界回归。 *)

Let normalize (t : Tm Γ A)
  : Nf Γ A
  := nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t.

(** Soundness constructs evidence at the signature bound, strictly below
    semantic values and world laws. *)

(** 可靠性在签名界限处构造证据，严格低于语义值与世界定律。 *)

Definition smaller_evidence_soundness (t : Tm Γ A)
  : TmEq@{b b _} t (embed_nf (normalize t))
  := nf_sound t.

(** Both directions of the Type-valued characterization use these exact
    bounds, including the direction that constructs equational evidence. *)

(** Type 值刻画的两个方向都使用这些指定界限，包括构造等式证据的方向。 *)

Definition smaller_evidence_characterization (t u : Tm Γ A)
  : TmEq@{b b _} t u ↔ normalize t = normalize u
  := tm_eq_nf t u.

(** The idempotence law preserves the same chosen semantic instance. *)

(** 幂等律保留同一个选定语义实例。 *)

Definition separated_idempotence (t : Tm Γ A)
  : normalize (embed_nf (normalize t)) = normalize t
  := nf_idempotent t.

End SmallerEvidence.

Section LargerEvidenceAndSmallerWorldLaws.
Universes b r l s e.
Constraint b < r.
Constraint r < l.
Constraint l < s.
Constraint s < e.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B).

(** Here world laws lie below semantic values, and equational evidence
    lies strictly above both. The logical relation uses an auxiliary
    bound; it must not collapse any of these named levels. *)

(** 此处世界定律低于语义值，等式证据又严格高于二者。逻辑关系使用辅助界限，
    不得合并这些命名层级。 *)

Let normalize (t : Tm Γ A)
  : Nf Γ A
  := nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t.

Definition larger_evidence_soundness (t : Tm Γ A)
  : TmEq@{b e _} t (embed_nf (normalize t))
  := nf_sound t.

Definition larger_evidence_characterization (t u : Tm Γ A)
  : TmEq@{b e _} t u ↔ normalize t = normalize u
  := tm_eq_nf t u.

Definition larger_evidence_from_normal_equality
    (t u : Tm Γ A) (h : normalize t = normalize u)
  : TmEq@{b e _} t u
  := nf_eq_tm_eq t u h.

End LargerEvidenceAndSmallerWorldLaws.
