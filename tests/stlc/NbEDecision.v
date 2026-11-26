From Cats Require Import
  STLC.Normalization
  STLC.NormalDecision
  STLC.Equivalence.
From Cats.Set Require Import Decision.
From Stdlib Require Import Arith.PeanoNat.

(** * Constructive Decision Interface Regressions *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Independent Decision and Fiber Bounds

    Fix [P : Type@{p}], [Q : Type@{q}] and two implication maps with
    [p < q]. Check decisions in both directions and dependent-fiber
    injection with either ordering of index and fiber sizes. *)

Section IndependentDecisionBounds.
Universes p q.
Constraint p < q.
Context (P : Type@{p}) (Q : Type@{q}) (h : P ↔ Q).

(** Decision transfer works from larger witnesses to smaller witnesses,
    and in the reverse direction. No universe resizing is involved. *)

Definition lower_decision (d : Decision Q)
  : Decision P
  := decision_iff h d.

Definition higher_decision (d : Decision P)
  : Decision Q
  := decision_iff (snd h, fst h) d.

(** Index size and fiber size are independent in either ordering. *)

Definition smaller_indices (I : Type@{p}) (F : I → Type@{q})
    (d : ∀ i j : I, Decision (i = j)) (i : I) (x y : F i)
    (e : existT F i x = existT F i y)
  : x = y
  := decidable_fiber_injective d F i x y e.

Definition larger_indices (I : Type@{q}) (F : I → Type@{p})
    (d : ∀ i j : I, Decision (i = j)) (i : I) (x y : F i)
    (e : existT F i x = existT F i y)
  : x = y
  := decidable_fiber_injective d F i x y e.

End IndependentDecisionBounds.

(** ** Decisions with Small Equational Evidence

    Fix [B], its label equality decision, contexts and terms with
    [b < r < s < l]. Check the complete beta/eta decision at evidence [b]. *)

Section SmallerEvidence.
Universes b r s l.
Constraint b < r.
Constraint r < s.
Constraint s < l.
Context (B : Type@{b}) (d : ∀ p q : B, Decision (p = q))
    (Γ : Ctx B) (A : Ty B) (t u : Tm Γ A).

(** Fix the semantic instance hidden by the decision's equational result.
    Evidence can live at the signature bound, below all semantic bounds. *)

Definition smaller_evidence_decision
  : Decision (TmEq@{b b _} t u)
  := tm_eq_decision@{b r s l b
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} d t u.

End SmallerEvidence.

(** ** Decisions with Larger Evidence

    Fix the same kinds of inputs with [b < r < l < s < e]. Check the
    complete decision with evidence above semantic values and world laws. *)

Section LargerEvidenceAndSmallerWorldLaws.
Universes b r l s e.
Constraint b < r.
Constraint r < l.
Constraint l < s.
Constraint s < e.
Context (B : Type@{b}) (d : ∀ p q : B, Decision (p = q))
    (Γ : Ctx B) (A : Ty B) (t u : Tm Γ A).

(** World laws may lie below semantic values, while the returned positive
    or negative equational witness lies above both. *)

Definition larger_evidence_decision
  : Decision (TmEq@{b e _} t u)
  := tm_eq_decision@{b r s l e
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} d t u.

End LargerEvidenceAndSmallerWorldLaws.

(** Inspect just the selected alternative, retaining witnesses in the
    actual decision interface. *)

Definition decision_tag {P : Type} (d : Decision P)
  : bool
  := match d with inl _ => true | inr _ => false end.

(** The computational examples explicitly choose natural-number labels. *)

Definition nat_label_decision (p q : nat)
  : Decision (p = q)
  := decision_of_sumbool (Nat.eq_dec p q).

(** Function beta is recognized for an open argument. *)

Example beta_decides
  : decision_tag (tm_eq_decision nat_label_decision
      ((ƛ (# var_zero)) · (# var_zero) : Tm (∅ ▻ ty_base 0) _)
      (# var_zero)) = true.
Proof. reflexivity. Qed.

(** Function eta is recognized after introducing a binder. *)

Example function_eta_decides
  : decision_tag (tm_eq_decision nat_label_decision
      (# var_zero : Tm (∅ ▻ (ty_base 0 ⇒ ty_base 1)) _)
      (ƛ ((# (var_succ var_zero)) · (# var_zero)))) = true.
Proof. reflexivity. Qed.

(** Product and unit eta identify open terms with their canonical shape. *)

Example product_eta_decides
  : decision_tag (tm_eq_decision nat_label_decision
      (# var_zero : Tm (∅ ▻ (ty_base 0 × ty_base 1)) _)
      (⟨π₁ (# var_zero), π₂ (# var_zero)⟩)) = true.
Proof. reflexivity. Qed.

Example unit_eta_decides
  : decision_tag (tm_eq_decision nat_label_decision
      (# var_zero : Tm (∅ ▻ ⊤) ⊤) ⋆) = true.
Proof. reflexivity. Qed.

(** Distinct variable positions remain distinct, even at identical types. *)

Example different_variables_decide
  : decision_tag (tm_eq_decision nat_label_decision
      (# var_zero : Tm ((∅ ▻ ty_base 0) ▻ ty_base 0) _)
      (# (var_succ var_zero))) = false.
Proof. reflexivity. Qed.

(** Blocked projections of a neutral product retain their distinct tags. *)

Example different_projections_decide
  : decision_tag (tm_eq_decision nat_label_decision
      (π₁ (# var_zero) : Tm (∅ ▻ (ty_base 0 × ty_base 0)) _)
      (π₂ (# var_zero))) = false.
Proof. reflexivity. Qed.

(** Comparison descends through lambdas without confusing a fresh variable
    with a weakened free variable. *)

Example different_bodies_decide
  : decision_tag (tm_eq_decision nat_label_decision
      (ƛ (# var_zero) : Tm (∅ ▻ ty_base 0) (ty_base 0 ⇒ ty_base 0))
      (ƛ (# (var_succ var_zero)))) = false.
Proof. reflexivity. Qed.

(** A shared blocked function still distinguishes different arguments. *)

Example different_arguments_decide
  : decision_tag (tm_eq_decision nat_label_decision
      ((# (var_succ (var_succ var_zero))) · (# var_zero) :
        Tm (((∅ ▻ (ty_base 0 ⇒ ty_base 0)) ▻ ty_base 0) ▻ ty_base 0) _)
      ((# (var_succ (var_succ var_zero))) ·
        (# (var_succ var_zero)))) = false.
Proof. reflexivity. Qed.

(** Equal result types can hide different application-domain annotations. *)

Example different_domains_decide
  : decision_tag (tm_eq_decision nat_label_decision
      ((# (var_succ (var_succ (var_succ var_zero)))) ·
        (# (var_succ var_zero)) :
        Tm ((((∅ ▻ (ty_base 0 ⇒ ty_base 2)) ▻ (ty_base 1 ⇒ ty_base 2)) ▻
          ty_base 0) ▻ ty_base 1) _)
      ((# (var_succ (var_succ var_zero))) · (# var_zero))) = false.
Proof. reflexivity. Qed.
