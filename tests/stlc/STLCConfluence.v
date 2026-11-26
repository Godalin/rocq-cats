From Cats.STLC Require Import BetaEtaLocal.

(** * Beta Confluence and Mixed-Peak Regressions

    Check the public results at separated and equal universes. Concrete
    critical peaks observe duplication, erasure and eta residual work by
    computing the common reduct and path lengths. These are interface
    regressions, not alternative proofs of the general theorems. *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Separate Computational Levels

    Fix [b < e < p < l]. No syntax/edge or edge/path identification is
    allowed, for either beta confluence or the mixed local diagram. *)

Section SeparateLevels.
Universes b e p l.
Constraint b < e, e < p, p < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The beta theorem returns joins at the requested path bound. *)

Definition separated_beta_confluence
  : is_confluent@{b e p p} (@BetaStep@{b e l b} B Γ A)
  := beta_confluent Γ A.

(** Mixed peaks retain beta and eta edge tags in the residual paths. *)

Definition separated_mixed_peak
  : is_locally_joinable@{b e e e p p}
      (@BetaStep@{b e l b} B Γ A) (@EtaContractStep@{b e l} B Γ A)
      (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_locally_joinable Γ A.

End SeparateLevels.

(** ** Paths above Classification

    Fix [b < e < l < p]. The edge-classification bound must not constrain
    the output paths. *)

Section LargePaths.
Universes b e l p.
Constraint b < e, e < l, l < p.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Beta confluence permits paths above the classification bound. *)

Definition large_beta_confluence
  : is_confluent@{b e p p} (@BetaStep@{b e l b} B Γ A)
  := beta_confluent Γ A.

(** The mixed theorem has the same independence. *)

Definition large_mixed_peak
  : is_locally_joinable@{b e e e p p}
      (@BetaStep@{b e l b} B Γ A) (@EtaContractStep@{b e l} B Γ A)
      (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_locally_joinable Γ A.

End LargePaths.

(** ** Equal Levels

    Syntax, steps and paths can share [b], with only [b < l]. *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Equal computational bounds remain supported. *)

Definition equal_beta_confluence
  : is_confluent@{b b b b} (@BetaStep@{b b l b} B Γ A)
  := beta_confluent Γ A.

(** No strict separation is needed for mixed peaks either. *)

Definition equal_mixed_peak
  : is_locally_joinable@{b b b b b b}
      (@BetaStep@{b b l b} B Γ A) (@EtaContractStep@{b b l} B Γ A)
      (@BetaEtaContractStep@{b b l} B Γ A)
  := beta_eta_locally_joinable Γ A.

End EqualLevels.

(** ** Explicit Residual Paths

    Use an empty base signature and closed unit terms. Count path edges
    without comparing their witnesses. All checks below compute by native
    reflexivity, including the duplicated eta argument. *)

Section ResidualPaths.

(** Count edges of any finite path. *)

Fixpoint path_length {X : Type} {R : crelation X} {x y : X}
    (p : (R^*) x y)
  : nat
  := match p with rtc_refl _ => 0 | rtc_cons _ q => S (path_length q) end.

(** A closed beta redex of unit type. *)

Definition unit_redex
  : Tm (ctx_empty : Ctx Empty_set) ⊤
  := (ƛ (# var_zero)) · ⋆.

(** A root projection discards a beta step in its other component. *)

Example discarded_beta_peak
  : let h := beta_root_join (root_beta_fst unit_redex unit_redex)
      (beta_step_lift op_fst (beta_step_lift (op_pair_r unit_redex)
        (context_step_root _ (root_beta_function (# var_zero) ⋆)))) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (unit_redex, 0, 1).
Proof. reflexivity. Defined.

(** A root projection retains a beta step in its selected component. *)

Example retained_beta_peak
  : let h := beta_root_join (root_beta_fst unit_redex unit_redex)
      (beta_step_lift op_fst (beta_step_lift (op_pair_l unit_redex)
        (context_step_root _ (root_beta_function (# var_zero) ⋆)))) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (⋆, 1, 1).
Proof. reflexivity. Defined.

(** A product-valued redex duplicates its unit argument. *)

Definition pair_redex
  : Tm (ctx_empty : Ctx Empty_set) (⊤ × ⊤)
  := (ƛ (⟨# var_zero, # var_zero⟩)) · ⋆.

(** Eta at the root and beta in one projection leave a second beta
    copy, followed by eta. Both legs are computed explicitly. *)

Example mixed_product_peak
  : let h := eta_root_beta_join (root_eta_contract_product pair_redex)
      (beta_step_lift (op_pair_l (π₂ pair_redex))
        (beta_step_lift op_fst (context_step_root _
          (root_beta_function (⟨# var_zero, # var_zero⟩) ⋆)))) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (⟨⋆, ⋆⟩, 1, 2).
Proof. reflexivity. Defined.

(** Beta duplicates an eta-redex argument. Two eta residuals remain on
    the beta side; the eta side takes the single root beta step. *)

Example duplicated_eta_peak
  : let body := (⟨# var_zero, # var_zero⟩ :
      Tm ((ctx_empty : Ctx Empty_set) ▻ (⊤ × ⊤))
        ((⊤ × ⊤) × (⊤ × ⊤))) in
    let arg := (⟨π₁ pair_redex, π₂ pair_redex⟩) in
    let h := beta_root_eta_join (root_beta_function body arg)
      (eta_contract_lift (op_app_r (ƛ body))
        (eta_contract_root (root_eta_contract_product pair_redex))) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (⟨pair_redex, pair_redex⟩, 2, 1).
Proof. reflexivity. Defined.

End ResidualPaths.
