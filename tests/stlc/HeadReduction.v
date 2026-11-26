From Cats.STLC Require Import EtaHead.
From CatsTests.stlc Require Import
  STLCConfluence.

(** * Head Strategy Interfaces and Product Eta Residuals

    Separate syntax, beta evidence, paths, trees and classification.
    Computation checks keep component types and contexts abstract; no
    label decision may be needed to compute the synchronized paths. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Small Selected Edges

    Even with a large signature the strategy certificate stays small. *)

Section LargeSignature.
Universe b.
Constraint Set < b.
Context {B : Type@{b}}.

(** Selection adds no signature-sized witness to its certificate. *)

Definition small_selected_edge {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
    (h : head_contractum t = Some u)
  : HeadBetaStep@{b} t u
  := {|head_beta_observation := h|}.

End LargeSignature.

(** ** Strategy Paths below Beta Evidence

    Fix [b < p < e < s < l]. A selected path stores small observations,
    so normalizing a supplied beta SN tree requires no [e <= p]. *)

Section SmallStrategyPaths.
Universes b p e s l.
Constraint b < p, p < e, e < s, s < l.
Context {B : Type@{b}}.

(** The output omits the larger beta edge and tree witnesses. *)

Definition strategy_path_below_beta {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
    (tree : SN@{b e s} BetaStep@{b e l b} t)
  : HeadResult@{b p} t
  := head_normalize_sn t tree.

End SmallStrategyPaths.

(** ** Paths below Trees

    Fix [b < e < p < s < l]. The supplied full beta tree builds only a
    path-sized result; it need not fit inside the result universe. *)

Section SmallPaths.
Universes b e p s l.
Constraint b < e, e < p, p < s, s < l.
Context {B : Type@{b}}.

(** The chosen-step certificate maps into independently sized beta. *)

Definition separated_head_beta {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : HeadBetaStep t u)
  : BetaStep@{b e l b} t u
  := head_beta_step_beta h.

(** No tree/path universe collapse occurs at the normalizer. *)

Definition small_path_head_result {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
    (tree : SN@{b e s} BetaStep@{b e l b} t)
  : HeadResult@{b p} t
  := head_normalize_sn t tree.

(** The residual obligation applies only at head-terminal eliminations. *)

Definition small_path_root_interface
    (remaining : @is_eta_head_elimination_root_joinable@{b e p l} B)
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots_of_head_eliminations remaining.

End SmallPaths.

(** ** Paths above Trees and Classification

    Reverse the ordering: [b < e < s < l < p]. Tree and classification
    bounds remain smaller than the independently sized output path. *)

Section LargePaths.
Universes b e p s l.
Constraint b < e, e < s, s < l, l < p.
Context {B : Type@{b}}.

(** Construct the same endpoint interface with the reversed bounds. *)

Definition large_path_head_result {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
    (tree : SN@{b e s} BetaStep@{b e l b} t)
  : HeadResult@{b p} t
  := head_normalize_sn t tree.

(** Path synchronization works independently of the beta tree bound. *)

Definition large_path_pair_join {Γ : Ctx B} {A U : Ty B}
    (t v : Tm Γ (A × U)) (a : Tm Γ A) (u : Tm Γ U)
    (path : ReflTransClos@{b Set p} HeadBetaStep t (⟨a, u⟩))
    (root : RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v)
  : Join@{b e p} BetaStep@{b e l b} t v
  := eta_product_root_beta_join_of_head_pair t v a u path root.

End LargePaths.

(** ** Transparent Residuals at Abstract Types

    Syntax, beta evidence, paths and trees share [b] here; classification
    remains above it. Native reflexivity checks actual residual data. *)

Section Computation.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A U V W : Ty B}.

(** A projection target reaching a pair has two one-step beta paths. *)

Definition projection_pair_join (a : Tm Γ A) (u : Tm Γ U) (z : Tm Γ V)
  : Join@{b b b} BetaStep@{b b l b}
      (π₁ (⟨⟨a, u⟩, z⟩)) (π₁ (⟨⟨a, u⟩, z⟩)).
Proof.
  refine (eta_product_root_beta_join_of_head_pair
      (π₁ (⟨⟨a, u⟩, z⟩)) (π₁ (⟨⟨a, u⟩, z⟩)) a u
      _ (root_eta_contract_product _)).
  apply rtc_step. refine {|head_beta_observation := _|}. reflexivity.
Defined.

(** The common pair and both residual lengths compute under abstraction. *)

Definition projection_pair_computes (a : Tm Γ A) (u : Tm Γ U)
    (z : Tm Γ V)
  : (projT1 (projection_pair_join a u z),
      (path_length (fst (projT2 (projection_pair_join a u z))),
       path_length (snd (projT2 (projection_pair_join a u z))))) =
      (⟨a, u⟩, (1, 1)).
Proof. reflexivity. Defined.

(** An application target reaches the newest variable by identity beta. *)

Definition application_var_join
  : Join@{b b b} (@BetaStep@{b b l b} B (Γ ▻ (A × U)) (A × U))
      ((ƛ (# var_zero)) · (# var_zero))
      ((ƛ (# var_zero)) · (# var_zero)).
Proof.
  refine (eta_product_root_beta_join_of_head_var
      ((ƛ (# var_zero)) · (# var_zero))
      ((ƛ (# var_zero)) · (# var_zero)) (@var_zero B Γ (A × U))
      _ (root_eta_contract_product _)).
  apply rtc_step. refine {|head_beta_observation := _|}. reflexivity.
Defined.

(** Both application residuals compute to one beta step. *)

Definition application_var_computes
  : (projT1 application_var_join,
      (path_length (fst (projT2 application_var_join)),
       path_length (snd (projT2 application_var_join)))) =
      (# var_zero, (1, 1)).
Proof. reflexivity. Defined.

(** Search through one principal child, then contract the exposed root. *)

Definition nested_projection_join (a : Tm Γ A) (u : Tm Γ U)
    (z : Tm Γ V) (w : Tm Γ W)
  : Join@{b b b} BetaStep@{b b l b}
      (π₂ (π₁ (⟨⟨z, ⟨a, u⟩⟩, w⟩)))
      (π₂ (π₁ (⟨⟨z, ⟨a, u⟩⟩, w⟩))).
Proof.
  refine (eta_product_root_beta_join_of_head_pair
      (π₂ (π₁ (⟨⟨z, ⟨a, u⟩⟩, w⟩)))
      (π₂ (π₁ (⟨⟨z, ⟨a, u⟩⟩, w⟩))) a u
      _ (root_eta_contract_product _)).
  refine (rtc_cons (y := π₂ (⟨z, ⟨a, u⟩⟩)) _ _).
  - refine {|head_beta_observation := _|}. reflexivity.
  - apply rtc_step. refine {|head_beta_observation := _|}. reflexivity.
Defined.

(** The two selected steps survive synchronization and mapping to beta. *)

Definition nested_projection_computes (a : Tm Γ A) (u : Tm Γ U)
    (z : Tm Γ V) (w : Tm Γ W)
  : (projT1 (nested_projection_join a u z w),
      (path_length (fst (projT2 (nested_projection_join a u z w))),
       path_length (snd (projT2 (nested_projection_join a u z w))))) =
      (⟨a, u⟩, (2, 2)).
Proof. reflexivity. Defined.

(** Head termination does not inspect a blocked function's argument. *)

Definition blocked_argument_is_not_searched
    (f : Var Γ (V ⇒ (A × U))) (a : Tm Γ V)
  : head_contractum ((# f) · ((ƛ (# var_zero)) · a)) = None.
Proof. reflexivity. Defined.

End Computation.
