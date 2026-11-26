From Cats.STLC Require Import BetaEtaConfluence.
From CatsTests.stlc Require Import
  STLCConfluence.

(** * Eta Diagrams with Independent Path Bounds

    These regressions retain the remaining product-root premise explicitly.
    They check the assembled interface with paths both below and above
    classification, and the unconditional weakening-reflection interface.
    Pair-root recovery also checks equal bounds and transparent residuals
    without evaluating the remaining non-pair operation. *)

Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Paths below Classification

    Fix [b < e < p < l]. No diagram may force paths to contain [l]. *)

Section SmallPaths.
Universes b e p l.
Constraint b < e, e < p, p < l.
Context {B : Type@{b}}.
Context (roots : @is_eta_product_root_joinable@{b e p l} B).

(** The remaining premise suffices at the smaller path bound. *)

Definition small_path_conditional_confluence (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent_of_product_roots roots Γ A.

(** Weakening reflection does not require the product-root premise. *)

Definition separated_eta_weakening {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ U) (u : Tm (Γ ▻ A) U)
    (h : EtaContractStep@{b e l} t⟨wkRen⟩ u)
  : ∃ v, EtaContractStep@{b e l} t v ∧ u = v⟨wkRen⟩
  := eta_contract_weaken_inv t u h.

(** A displayed pair determines its root target even at separated
    syntax and evidence bounds. *)

Definition separated_product_pair_unique {Γ : Ctx B} {A U : Ty B}
    (a : Tm Γ A) (u : Tm Γ U) (v : Tm Γ (ty_prod A U))
    (h : RootEtaContract@{b e}
      (⟨π₁ (⟨a, u⟩), π₂ (⟨a, u⟩)⟩) v)
  : ⟨a, u⟩ = v
  := root_eta_product_pair_unique a u v h.

(** Only the non-pair input is needed to recover the original interface
    with paths below classification. It remains an explicit premise. *)

Definition small_path_nonpair_confluence
    (nonpairs : @is_eta_nonpair_product_root_joinable@{b e p l} B)
    (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent_of_product_roots
      (eta_product_roots_of_nonpairs nonpairs) Γ A.

End SmallPaths.

(** ** Paths above Classification

    Fix [b < e < l < p]. Classification must not contain the path bound. *)

Section LargePaths.
Universes b e l p.
Constraint b < e, e < l, l < p.
Context {B : Type@{b}}.
Context (roots : @is_eta_product_root_joinable@{b e p l} B).

(** The opposite ordering supports the same explicit-premise theorem. *)

Definition large_path_conditional_confluence (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent_of_product_roots roots Γ A.

(** The restriction also suffices when paths exceed classification. *)

Definition large_path_nonpair_confluence
    (nonpairs : @is_eta_nonpair_product_root_joinable@{b e p l} B)
    (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent_of_product_roots
      (eta_product_roots_of_nonpairs nonpairs) Γ A.

End LargePaths.

(** ** Equal Bounds and Transparent Pair Recovery

    Fix equal syntax, evidence and path bounds, with only classification
    larger. The non-pair operation stays abstract: resolving a pair root
    must not call it, and the resulting common reduct computes directly. *)

Section EqualBounds.
Universes b l.
Constraint b < l.
Context {B : Type@{b}}.
Context (nonpairs : @is_eta_nonpair_product_root_joinable@{b b b l} B).

(** Neither the restriction nor the assembly requires a strict increase
    from syntax to edges or paths. *)

Definition equal_bound_product_roots
  : @is_eta_product_root_joinable@{b b b l} B
  := eta_product_roots_of_nonpairs nonpairs.

(** The abstract remaining operation is not forced at a pair root.
    Both computed residual paths are reflexive. *)

Example pair_root_recovery_computes {Γ : Ctx B} {A U : Ty B}
    (a : Tm Γ A) (u : Tm Γ U)
  : let pair := ⟨a, u⟩ in
    let h := equal_bound_product_roots Γ A U pair pair
      (root_eta_contract_product pair) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (pair, 0, 0).
Proof. reflexivity. Defined.

End EqualBounds.
