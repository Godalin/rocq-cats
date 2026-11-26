From Cats.STLC Require Import BetaEtaConfluence.
From CatsTests.stlc Require Import
  STLCConfluence.

(** * Product Variable Views and Eta Roots

    Check that variable views remain small at a large signature, and that
    variable eta roots retain separated evidence bounds. The remaining
    elimination operation is kept abstract in the path and computation
    regressions: it must not be evaluated for a variable root. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Small Views at a Large Signature

    Fix [Set < b]. The views, like the original variables, remain in
    [Set]; they do not store a newly sized copy of the context. *)

Section LargeSignature.
Universe b.
Constraint Set < b.
Context {B : Type@{b}}.

(** Both projections fit into a small pair. *)

Definition small_product_views {Γ : Ctx B} {A U : Ty B}
    (x : Var Γ (A × U))
  : (LeftProductVar Γ A * RightProductVar Γ U)%type
  := (product_var_left x, product_var_right x).

(** Their joint recovery does not identify the signature with [Set]. *)

Definition large_signature_recovery {Γ : Ctx B} {A U : Ty B}
    (x y : Var Γ (A × U))
    (h : fst (small_product_views x) = fst (small_product_views y))
    (k : snd (small_product_views x) = snd (small_product_views y))
  : x = y
  := product_var_projections_injective x y h k.

End LargeSignature.

(** ** Paths below Classification

    Fix [b < e < p < l]. Variable recovery must not force the evidence
    bound to equal the syntax bound, or paths to contain classification. *)

Section SmallPaths.
Universes b e p l.
Constraint b < e, e < p, p < l.
Context {B : Type@{b}}.

(** Root uniqueness has no remaining product-root premise. *)

Definition separated_variable_root {Γ : Ctx B} {A U : Ty B}
    (x : Var Γ (A × U)) (v : Tm Γ (A × U))
    (h : RootEtaContract@{b e} (⟨π₁ (# x), π₂ (# x)⟩) v)
  : # x = v
  := root_eta_product_var_unique x v h.

(** Only targets with both observations absent need residual paths. *)

Definition small_path_elimination_roots
    (remaining : ∀ (Γ : Ctx B) (A U : Ty B) (t v : Tm Γ (A × U)),
      RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v →
      pair_parts t = None → variable_position t = None →
      Join@{b e p} BetaEtaContractStep@{b e l} t v)
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots_of_eliminations remaining.

End SmallPaths.

(** ** Paths above Classification

    Fix [b < e < l < p]. The same residual interface supports the opposite
    ordering without changing the root-recovery construction. *)

Section LargePaths.
Universes b e l p.
Constraint b < e, e < l, l < p.
Context {B : Type@{b}}.

(** The larger path bound need not fit below classification. *)

Definition large_path_elimination_roots
    (remaining : ∀ (Γ : Ctx B) (A U : Ty B) (t v : Tm Γ (A × U)),
      RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v →
      pair_parts t = None → variable_position t = None →
      Join@{b e p} BetaEtaContractStep@{b e l} t v)
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots_of_eliminations remaining.

End LargePaths.

(** ** Computing Newest and Older Variable Roots

    Fix equal syntax, evidence and path bounds, with only classification
    larger. The component types and context stay abstract. The remaining
    elimination operation must not be forced for either variable position. *)

Section VariableComputations.
Universes b l.
Constraint b < l.
Context {B : Type@{b}}.
Context (remaining : ∀ (Γ : Ctx B) (A U : Ty B) (t v : Tm Γ (A × U)),
  RootEtaContract@{b b} (⟨π₁ t, π₂ t⟩) v →
  pair_parts t = None → variable_position t = None →
  Join@{b b b} BetaEtaContractStep@{b b l} t v).

(** The interface works at equal computational bounds. *)

Definition equal_bound_elimination_roots
  : @is_eta_product_root_joinable@{b b b l} B
  := eta_product_roots_of_eliminations remaining.

(** The newest variable is recovered with two empty residual paths. *)

Example newest_variable_root_computes {Γ : Ctx B} {A U : Ty B}
  : let t := (# (var_zero : Var (Γ ▻ (A × U)) (A × U))) in
    let h := equal_bound_elimination_roots (Γ ▻ (A × U)) A U t t
      (root_eta_contract_product t) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (t, 0, 0).
Proof. reflexivity. Defined.

(** Adding an unrelated newest declaration keeps the old position. *)

Example older_variable_root_computes {Γ : Ctx B} {A U V : Ty B}
  : let t := (# (var_succ var_zero :
      Var (Γ ▻ (A × U) ▻ V) (A × U))) in
    let h := equal_bound_elimination_roots (Γ ▻ (A × U) ▻ V) A U t t
      (root_eta_contract_product t) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (t, 0, 0).
Proof. reflexivity. Defined.

(** Equal declaration types do not identify different positions. *)

Example product_views_distinguish_positions {Γ : Ctx B} {A U : Ty B}
  : product_var_left (var_succ var_zero :
      Var (Γ ▻ (A × U) ▻ (A × U)) (A × U)) <>
      product_var_left (var_zero :
        Var (Γ ▻ (A × U) ▻ (A × U)) (A × U)).
Proof. discriminate. Defined.

End VariableComputations.
