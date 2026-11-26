From Cats.STLC Require Import EtaCompletion.
From CatsTests.stlc Require Import
  STLCConfluence.

(** * Completed Beta/Eta Interfaces and Blocked-Head Computations

    The confluence interfaces below have no product-root premise. Check
    both strict path/classification orders and equal computational bounds.
    Endpoint computations retain abstract raw arguments and type labels. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Recovery under a Large Signature

    Fix [Set < b]. Joint recovery must not make the signature small or
    resize stored raw arguments and their markers. *)

Section LargeSignature.
Universe b.
Constraint Set < b.
Context {B : Type@{b}} {Γ Δ : Ctx B} {D A U : Ty B}.

(** Two projected spine codes recover the whole original code. *)

Definition large_signature_spine_recovery
    (p q : AlignedSpine Γ D (A × U))
    (left : spine_fst p = spine_fst q)
    (right : spine_snd p = spine_snd q)
  : p = q
  := spine_projections_injective Γ D p q left right.

(** Position tags remain part of recovery at the same signature bound. *)

Definition large_signature_position_recovery
    (p q : VariableSpine Γ Δ (A × U))
    (left : variable_spine_fst Γ Δ A U p = variable_spine_fst Γ Δ A U q)
    (right : variable_spine_snd Γ Δ A U p = variable_spine_snd Γ Δ A U q)
  : p = q
  := variable_spine_projections_injective Γ Δ p q left right.

End LargeSignature.

(** ** Paths below Trees and Classification

    Fix [b < e < p < s < l]. The constructed root diagrams and global
    theorem need no supplied diagram, despite their independent bounds. *)

Section SmallPaths.
Universes b e p s l.
Constraint b < e, e < p, p < s, s < l.
Context {B : Type@{b}}.

(** The original product-root interface is now populated. *)

Definition small_path_completed_roots
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots.

(** Eta/eta diagrams may have mixed residual paths. *)

Definition small_path_eta_diagrams (Γ : Ctx B) (A : Ty B)
  : is_locally_joinable@{b e e e p _}
      (@EtaContractStep@{b e l} B Γ A) (@EtaContractStep@{b e l} B Γ A)
      (@BetaEtaContractStep@{b e l} B Γ A)
  := eta_eta_joinable Γ A.

(** Local confluence has no remaining assumption. *)

Definition small_path_local_confluence (Γ : Ctx B) (A : Ty B)
  : is_locally_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_locally_confluent Γ A.

(** Global confluence keeps the smaller path bound. *)

Definition small_path_completed_confluence (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent Γ A.

(** Uniqueness requires only supplied paths and irreducible endpoints. *)

Definition small_path_completed_uniqueness
    {Γ : Ctx B} {A : Ty B} {t u v : Tm Γ A}
    (h : ReflTransClos@{b e p} BetaEtaContractStep@{b e l} t u)
    (k : ReflTransClos@{b e p} BetaEtaContractStep@{b e l} t v)
    (hu : is_irreducible BetaEtaContractStep@{b e l} u)
    (hv : is_irreducible BetaEtaContractStep@{b e l} v)
  : u = v
  := beta_eta_irreducible_unique h k hu hv.

End SmallPaths.

(** ** Paths above Trees and Classification

    Reverse the order to [b < e < s < l < p]. No implicit dependency
    should require normalization trees or classification to contain paths. *)

Section LargePaths.
Universes b e p s l.
Constraint b < e, e < s, s < l, l < p.
Context {B : Type@{b}}.

(** Construct the same root interface in the reverse order. *)

Definition large_path_completed_roots
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots.

(** The global theorem also accepts the larger path bound. *)

Definition large_path_completed_confluence (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent Γ A.

End LargePaths.

(** ** Equal Bounds and Transparent Blocked Endpoints

    Syntax, edge, path and tree bounds may coincide. Classification alone
    remains larger. The endpoint join must compute while raw arguments,
    contexts and component types stay abstract. *)

Section Computation.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A U V : Ty B}.

(** Equal computational bounds support unconditional confluence. *)

Definition equal_bound_completed_confluence
  : is_confluent@{b b b _} (@BetaEtaContractStep@{b b l} B Γ A)
  := beta_eta_confluent Γ A.

(** A blocked function keeps an unreduced identity application as argument. *)

Definition blocked_argument_root_join
    (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : let t := (# var_zero) · ((ƛ (# var_zero)) · a) in
    Join@{b b b} BetaEtaContractStep@{b b l} t t
  := let t := (# var_zero) · ((ƛ (# var_zero)) · a) in
     eta_head_elimination_roots _ _ _ t t
       (root_eta_contract_product t) eq_refl eq_refl eq_refl.

(** The common target keeps that redex and both paths are empty. *)

Definition blocked_argument_root_computes
    (a : Tm (Γ ▻ (V ⇒ (A × U))) V)
  : let h := blocked_argument_root_join a in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) =
    ((# var_zero) · ((ƛ (# var_zero)) · a), 0, 0).
Proof. reflexivity. Defined.

(** Nested projected heads use the same zero-step endpoint operation. *)

Definition nested_projection_root_join
  : let t := π₂ (π₁ (# (@var_zero B Γ ((V × (A × U)) × V)))) in
    Join@{b b b} BetaEtaContractStep@{b b l} t t
  := let t := π₂ (π₁ (# (@var_zero B Γ ((V × (A × U)) × V)))) in
     eta_head_elimination_roots _ _ _ t t
       (root_eta_contract_product t) eq_refl eq_refl eq_refl.

(** The nested raw head and both empty paths compute by reflexivity. *)

Definition nested_projection_root_computes
  : (projT1 nested_projection_root_join,
      path_length (fst (projT2 nested_projection_root_join)),
      path_length (snd (projT2 nested_projection_root_join))) =
    (π₂ (π₁ (# (@var_zero B Γ ((V × (A × U)) × V)))), 0, 0).
Proof. reflexivity. Defined.

(** A selected older position remains distinct from an equal declaration. *)

Definition older_function_root_join
    (a : Tm (Γ ▻ (V ⇒ (A × U)) ▻ (V ⇒ (A × U))) V)
  : let t := (# (var_succ var_zero)) · a in
    Join@{b b b} BetaEtaContractStep@{b b l} t t
  := let t := (# (var_succ var_zero)) · a in
     eta_head_elimination_roots _ _ _ t t
       (root_eta_contract_product t) eq_refl eq_refl eq_refl.

(** Joint recovery does not collapse the two declaration positions. *)

Definition older_function_root_computes
    (a : Tm (Γ ▻ (V ⇒ (A × U)) ▻ (V ⇒ (A × U))) V)
  : let h := older_function_root_join a in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) =
    ((# (var_succ var_zero)) · a, 0, 0).
Proof. reflexivity. Defined.

End Computation.
