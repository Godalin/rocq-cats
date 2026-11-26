From Cats.STLC Require Import VariableSpine.

(** * Inferred Elimination-Spine Interfaces

    Check small markers, signature-sized raw views, independent fold
    result bounds and native reconstruction at abstract component types.
    Raw argument redexes and unit-valued blocked heads must survive. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** A Large Signature and Small Leaf Data

    Fix [Set < b]. Stored raw arguments may use [b], while binding
    markers and a fold's output can remain small. *)

Section LargeSignature.
Universe b.
Constraint Set < b.
Context {B : Type@{b}} {Γ Δ : Ctx B} {D A : Ty B}.

(** A view fits the original syntax bound, without raising it. *)

Definition signature_sized_view
  : Type@{b}
  := VariableSpine Γ Δ A.

(** Folding to a small value does not identify the signature with [Set]. *)

Definition small_fold_result (p : AlignedSpine Γ D A) (head : Tm Γ D)
  : nat
  := elimination_tree_fold Γ (λ _ _ _, 0) D p head.

End LargeSignature.

(** ** Independent Fold Targets

    Fix [b < k]. A fold can also compute in a larger target, independently
    of both its small leaf witnesses and signature-sized tree. *)

Section LargeFoldTarget.
Universes b k.
Constraint b < k.
Context {B : Type@{b}} {Γ : Ctx B} {D A : Ty B}.
Context {K : Type@{k}} (value : K).

(** The output level need not equal the raw-term level. *)

Definition large_fold_result (p : AlignedSpine Γ D A) (head : Tm Γ D)
  : K
  := elimination_tree_fold Γ (λ _ _ _, value) D p head.

End LargeFoldTarget.

(** ** Raw Reconstruction at Abstract Types

    Keep the signature, contexts, component types and raw arguments
    abstract. Context positions and head declarations are displayed,
    so the view and its embedding must compute without label decisions. *)

Section Computation.
Context {B : Type} {Γ : Ctx B} {A U V : Ty B}.

(** A variable function applied to a redex is still a blocked head. *)

Definition blocked_raw_argument (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : Tm (Γ ▻ (V ⇒ (A × U))) (A × U)
  := (# var_zero) · ((ƛ (# var_zero)) · a).

(** The view retains the redex as the canonical-domain argument. *)

Definition blocked_raw_argument_view (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : variable_spine_view (blocked_raw_argument a) =
      Some (inr (inr (((ƛ (# var_zero)) · a), inl new_var))).
Proof. reflexivity. Defined.

(** Re-embedding the explicit view reconstructs the original application. *)

Definition blocked_raw_argument_embeds (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : @embed_variable_view B (Γ ▻ (V ⇒ (A × U))) (A × U)
      (inr (inr (((ƛ (# var_zero)) · a), inl new_var))) =
      blocked_raw_argument a.
Proof. reflexivity. Defined.

(** The terminal classifier finds that same view without reducing [a]. *)

Definition blocked_raw_argument_classifies
    (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : projT1 (head_terminal_product_spine (blocked_raw_argument a)
      eq_refl eq_refl) =
      inr (inr (((ƛ (# var_zero)) · a), inl new_var)).
Proof. reflexivity. Defined.

(** A nested projection records the declared product branches. *)

Definition nested_projection_view
  : variable_spine_view
      (π₂ (π₁ (# (@var_zero B Γ ((V × (A × U)) × V))))) =
      Some (inr (inr (inl (inr (inr (inl new_var)))))).
Proof. reflexivity. Defined.

(** An older variable keeps its position even beside an equal declaration. *)

Definition older_function_view (a : Tm (Γ ▻ (V ⇒ A) ▻ (V ⇒ A)) V)
  : variable_spine_view ((# (var_succ var_zero)) · a) =
      Some (inl (inr (inr (a, inl new_var)))).
Proof. reflexivity. Defined.

(** Unit-valued blocked applications remain applications. *)

Definition unit_blocked_view (a : Tm (Γ ▻ (V ⇒ ⊤)) V)
  : variable_spine_view ((# var_zero) · a) =
      Some (inr (inr (a, inl new_var))).
Proof. reflexivity. Defined.

(** Pair introductions have no variable-headed spine, regardless of
    whether their components happen to be blocked. *)

Definition pair_has_no_spine (a : Tm Γ A) (u : Tm Γ U)
  : variable_spine_view (⟨a, u⟩) = None.
Proof. reflexivity. Defined.

End Computation.
