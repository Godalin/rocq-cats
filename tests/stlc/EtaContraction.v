From Cats.STLC Require Import EtaNormalization.
From Cats.Set.Relation Require Import Compatible.

(** * Eta-Contraction Interface Regressions

    Check that the numerical measure does not collapse carrier, edge and
    tree universes. Exercise contextual contraction under a binder, its
    transparent reversal, and the beta/eta coproduct's branch tags. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Measures with Large Edges

    Fix [a < e < s]. A small natural-number measure can construct large
    trees without resizing the relation's edge witnesses. *)

Section LargeEdges.
Universes a e s.
Constraint a < e, e < s.
Context {X : Type@{a}} (R : X → X → Type@{e}) (m : X → nat).
Context (decrease : ∀ x y, R x y → m y < m x).

(** The return type retains the requested large tree universe. *)

Definition large_edge_measure (x : X)
  : SN@{a e s} R x
  := sn_measure m decrease x.

End LargeEdges.

(** ** Measures with Large Carriers

    Fix [e < a < s] to check the opposite order of carrier and edge sizes. *)

Section LargeCarriers.
Universes e a s.
Constraint e < a, a < s.
Context {X : Type@{a}} (R : X → X → Type@{e}) (m : X → nat).
Context (decrease : ∀ x y, R x y → m y < m x).

(** Large carriers need not force the edge universe to grow. *)

Definition large_carrier_measure (x : X)
  : SN@{a e s} R x
  := sn_measure m decrease x.

End LargeCarriers.

(** ** Trees below Classification

    Fix [b < e < s < l]. Check all-term eta SN and preservation by
    substitution and renaming, with equation evidence still at [e]. *)

Section SmallTrees.
Universes b e s l.
Constraint b < e, e < s, s < l.
Context {B : Type@{b}} {Γ Δ : Ctx B} {A : Ty B}.

(** Eta trees may be smaller than relation classification. *)

Definition small_eta_tree (t : Tm Γ A)
  : SN@{b e s} (@EtaContractStep@{b e l} B Γ A) t
  := eta_strong_normalization t.

(** Arbitrary simultaneous substitutions preserve the chosen step. *)

Definition separated_eta_subst {t u : Tm Γ A}
    (h : EtaContractStep@{b e l} t u) (σ : Sub Δ Γ)
  : EtaContractStep@{b e l} t[σ] u[σ]
  := eta_contract_subst h Δ σ.

(** Renaming does not require an injective variable map. *)

Definition separated_eta_rename {t u : Tm Γ A}
    (h : EtaContractStep@{b e l} t u) (ρ : Ren Δ Γ)
  : EtaContractStep@{b e l} t⟨ρ⟩ u⟨ρ⟩
  := eta_contract_rename h Δ ρ.

(** Both coproduct branches have equation witnesses at the edge level. *)

Definition separated_beta_eta_sound {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e l} t u)
  : TmEq@{b e b} t u
  := beta_eta_contract_to_tm_eq h.

(** The coproduct's substitution map retains its independent edge size. *)

Definition separated_beta_eta_subst {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e l} t u) (σ : Sub Δ Γ)
  : BetaEtaContractStep@{b e l} t[σ] u[σ]
  := beta_eta_contract_subst h Δ σ.

(** The coproduct's renaming map has the same universe boundary. *)

Definition separated_beta_eta_rename {t u : Tm Γ A}
    (h : BetaEtaContractStep@{b e l} t u) (ρ : Ren Δ Γ)
  : BetaEtaContractStep@{b e l} t⟨ρ⟩ u⟨ρ⟩
  := beta_eta_contract_rename h Δ ρ.

End SmallTrees.

(** ** Trees above Classification

    Fix [b < e < l < s]; classification must not bound the SN tree. *)

Section LargeTrees.
Universes b e l s.
Constraint b < e, e < l, l < s.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The same theorem constructs a tree above the classification bound. *)

Definition large_eta_tree (t : Tm Γ A)
  : SN@{b e s} (@EtaContractStep@{b e l} B Γ A) t
  := eta_strong_normalization t.

End LargeTrees.

(** ** Equal Computational Levels

    Fix a common syntax, edge and tree bound [b], with only [b < l]. *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Strict separation of computational universes is optional. *)

Definition equal_eta_tree (t : Tm Γ A)
  : SN@{b b b} (@EtaContractStep@{b b l} B Γ A) t
  := eta_strong_normalization t.

End EqualLevels.

(** ** Transparent Contexts and Branches

    Use an empty base signature. Check actual node counts, contraction
    beneath a lambda and observable branch tags after witness maps. *)

Section Computations.

(** A free function whose eta expansion contains four nodes. *)

Definition free_function
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ ⇒ ⊤)) (⊤ ⇒ ⊤)
  := # var_zero.

(** The weakening in function eta does not add syntax nodes. *)

Example function_eta_size
  : tm_size (ƛ (free_function⟨wkRen⟩ · (# var_zero))) = 4
  := eq_refl.

(** A free product, used twice by its eta expansion. *)

Definition free_product
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤)) (⊤ × ⊤)
  := # var_zero.

(** Pairing and the two projections contribute three additional nodes. *)

Example product_eta_size
  : tm_size (⟨π₁ free_product, π₂ free_product⟩) = 5
  := eq_refl.

(** This witness contracts the weakened product under a fresh binder. *)

Definition binder_eta
  : EtaContractStep
      (ƛ (⟨π₁ free_product⟨ren_weaken (A := ⊤)⟩,
        π₂ free_product⟨wkRen⟩⟩)) (ƛ free_product⟨wkRen⟩)
  := eta_contract_lift op_lam
      (eta_contract_root (root_eta_contract_product free_product⟨wkRen⟩)).

(** Count enclosing operations to observe the reversal fold. *)

Fixpoint context_depth {I : Type} {X : I → Type}
    {K : ContextSystem X} {R : RelationFamily X}
    {i : I} {x y : X i} (h : ContextClos K R i x y)
  : nat
  := match h with
  | context_step _ => 0
  | context_lift _ p => S (context_depth p)
  end.

(** Reversal retains the one surrounding lambda, by computation. *)

Example reversed_binder_depth
  : context_depth (eta_contract_context binder_eta) = 1
  := eq_refl.

(** Reversing again still retains that surrounding operation. *)

Example restored_binder_depth
  : context_depth (context_eta_contract (eta_contract_context binder_eta)) = 1
  := eq_refl.

(** The subtree after this contextual contraction remains accessible. *)

Example binder_eta_subtree
  : SN EtaContractStep (ƛ free_product⟨ren_weaken (A := ⊤)⟩)
  := sn_step (eta_strong_normalization _) binder_eta.

(** Observe the coproduct tag without inspecting its stored proof. *)

Definition is_beta_branch {B : Type} {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : BetaEtaContractStep t u)
  : bool
  := match h with inl _ => true | inr _ => false end.

(** Substitution keeps the eta alternative even for a binder step. *)

Example subst_eta_tag
  : is_beta_branch (beta_eta_contract_subst (inr binder_eta) _ idSub) = false
  := eq_refl.

(** Renaming likewise keeps the beta alternative. *)

Example rename_beta_tag
  : is_beta_branch (beta_eta_contract_rename
      (inl (context_step_root _
        (root_beta_function (# var_zero)
          (⋆ : Tm (@ctx_empty Empty_set) ⊤)))) _ idRen) = true
  := eq_refl.

End Computations.
