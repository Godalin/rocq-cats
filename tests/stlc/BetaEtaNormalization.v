From Cats.STLC Require Import BetaEtaNormalization.

(** * Beta/Eta Normalization Regressions

    Check independent component and result trees, paths and edge sizes in
    the generic interaction theorem. Check the STLC result at separated
    and equal levels, and observe residual work in concrete overlap cases. *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Large Paths and Small Component Trees

    Fix [a < r < t < sr < st < s < p < k]. The two edge types, component
    trees, output tree, path and law bounds are all strictly separated. *)

Section LargePaths.
Universes a r t sr st s p k.
Constraint a < r, r < t, t < sr, sr < st, st < s, s < p, p < k.
Context {X : Type@{a}} (R : X → X → Type@{r}) (S : X → X → Type@{t}).
Context (commute : is_quasi_commuting@{a r t p k t} R S).
Context (normalS : ∀ x, SN@{a t st} S x).

(** Large paths do not force larger output trees. *)

Definition large_path_sum_sn {x : X} (h : SN@{a r sr} R x)
  : SN@{a t s} (R ⊕R S) x
  := sn_sum_quasi_commuting commute normalS h.

End LargePaths.

(** ** Large Inputs and Small Result Trees

    Fix [t < r < a < p < s < sr < st < k]. The edge order is reversed;
    paths and the result tree are smaller than either input tree. *)

Section LargeInputTrees.
Universes t r a p s sr st k.
Constraint t < r, r < a, a < p, p < s, s < sr, sr < st, st < k.
Context {X : Type@{a}} (R : X → X → Type@{r}) (S : X → X → Type@{t}).
Context (commute : is_quasi_commuting@{a r t p k r} R S).
Context (normalS : ∀ x, SN@{a t st} S x).

(** Recursion constructs the mixed tree without storing large input
    trees or path witnesses in the result. *)

Definition large_input_sum_sn {x : X} (h : SN@{a r sr} R x)
  : SN@{a r s} (R ⊕R S) x
  := sn_sum_quasi_commuting commute normalS h.

End LargeInputTrees.

(** ** Separate STLC Levels

    Fix [b < e < p < s < l]. The interaction produces paths at [p],
    whereas the final theorem returns trees at the independent [s]. *)

Section SeparatedLevels.
Universes b e p s l.
Constraint b < e, e < p, p < s, s < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The mixed theorem retains genuinely different syntax and edge sizes. *)

Definition separated_beta_eta_sn (t : Tm Γ A)
  : SN@{b e s} (@BetaEtaContractStep@{b e l} B Γ A) t
  := beta_eta_strong_normalization t.

(** The diagram itself is available at the requested path bound. *)

Definition separated_beta_eta_diagram {x y z : Tm Γ A}
    (h : EtaContractStep@{b e l} x y) (k : BetaStep@{b e l b} y z)
  : ∃ v, BetaStep@{b e l b} x v ∧
      ReflTransClos@{b e p} BetaEtaContractStep@{b e l} v z
  := beta_eta_quasi_commuting Γ A x y z h k.

End SeparatedLevels.

(** ** Trees above Classification

    Fix [b < e < l < s < p]. Step classification must not bound mixed
    trees or interaction paths. *)

Section LargeTrees.
Universes b e l s p.
Constraint b < e, e < l, l < s, s < p.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The result is independent of the classification/tree ordering. *)

Definition large_beta_eta_sn (t : Tm Γ A)
  : SN@{b e s} (@BetaEtaContractStep@{b e l} B Γ A) t
  := beta_eta_strong_normalization t.

(** Interaction paths may exceed both classification and tree bounds. *)

Definition large_beta_eta_diagram {x y z : Tm Γ A}
    (h : EtaContractStep@{b e l} x y) (k : BetaStep@{b e l b} y z)
  : ∃ v, BetaStep@{b e l b} x v ∧
      ReflTransClos@{b e p} BetaEtaContractStep@{b e l} v z
  := beta_eta_quasi_commuting Γ A x y z h k.

End LargeTrees.

(** ** Equal Computational Levels

    Syntax, edge and tree sizes may coincide, with only [b < l]. *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** No strict computational separation is required by the theorem. *)

Definition equal_beta_eta_sn (t : Tm Γ A)
  : SN@{b b b} (@BetaEtaContractStep@{b b l} B Γ A) t
  := beta_eta_strong_normalization t.

End EqualLevels.

(** ** Residual Work and Mixed Choices

    Fix an empty base signature. Product eta duplicates the beta source;
    root beta can in turn duplicate an eta-redex argument. Observe both
    phenomena without equating their derivation witnesses. *)

Section Residuals.

(** Count edges, preserving the distinction from an empty path. *)

Fixpoint path_length {X : Type} {R : X → X → Type}
    {x y : X} (h : (R^*) x y)
  : nat
  := match h with
  | rtc_refl _ => 0
  | rtc_cons _ tail => S (path_length tail)
  end.

(** A product beta redex with a free product argument. *)

Definition product_redex
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤)) (⊤ × ⊤)
  := (ƛ (# var_zero)) · (# var_zero).

(** The diagram's first beta changes one copy; its tail contains the
    other copy's beta followed by eta contraction. *)

Example product_residual_length
  : path_length (snd (projT2
      (root_eta_beta_diagram (root_eta_product product_redex)
        (# var_zero) (context_step_root _
          (root_beta_function (# var_zero) (# var_zero)))))) = 2
  := eq_refl.

(** A closed identity used in the enclosing application overlap. *)

Definition unit_identity
  : Tm (@ctx_empty Empty_set) (⊤ ⇒ ⊤)
  := ƛ (# var_zero).

(** Contracting the expanded lambda at the enclosing beta leaves one
    beta step, computed through the typed introduction observer. *)

Example enclosing_function_residual_length
  : path_length (snd (projT2
      (eta_expansion_root_context (op_app_l ⋆)
        (context_step_root _ (root_eta_function unit_identity))
        (root_beta_function (# var_zero) ⋆)))) = 1
  := eq_refl.

(** A free product fixes the signature and context of the argument case. *)

Definition product_variable
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤)) (⊤ × ⊤)
  := # var_zero.

(** Moving beta first duplicates the eta edge into two residual steps. *)

Example duplicated_argument_residual_length
  : path_length (snd (projT2
      (eta_expansion_root_context
        (op_app_r (ƛ (⟨# var_zero, # var_zero⟩)))
        (context_step_root _ (root_eta_product product_variable))
        (root_beta_function (⟨# var_zero, # var_zero⟩) product_variable)))) = 2
  := eq_refl.

(** A duplicator applied to an eta-expanded free product. *)

Definition duplicating_eta_argument
  : Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤))
      ((⊤ × ⊤) × (⊤ × ⊤))
  := (ƛ (⟨# var_zero, # var_zero⟩)) ·
      (⟨π₁ (# var_zero), π₂ (# var_zero)⟩).

(** The all-term tree includes eta in the argument followed by root beta. *)

Example eta_then_duplicating_beta_sn
  : SN BetaEtaContractStep
      (⟨# var_zero, # var_zero⟩ :
        Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤))
          ((⊤ × ⊤) × (⊤ × ⊤)))
  := sn_step
      (sn_step (beta_eta_strong_normalization duplicating_eta_argument)
        (inr (eta_contract_lift (op_app_r (ƛ (⟨# var_zero, # var_zero⟩)))
          (eta_contract_root (root_eta_contract_product (# var_zero))))))
      (inl (context_step_root _
        (root_beta_function (⟨# var_zero, # var_zero⟩) (# var_zero)))).

(** Beta may instead duplicate the expanded argument first. The mixed
    tree covers eta contraction independently in both resulting copies. *)

Example duplicated_eta_redexes_sn
  : SN BetaEtaContractStep
      (⟨⟨π₁ (# var_zero), π₂ (# var_zero)⟩,
        ⟨π₁ (# var_zero), π₂ (# var_zero)⟩⟩ :
        Tm ((@ctx_empty Empty_set) ▻ (⊤ × ⊤))
          ((⊤ × ⊤) × (⊤ × ⊤)))
  := sn_step (beta_eta_strong_normalization duplicating_eta_argument)
      (inl (context_step_root _ (root_beta_function
        (⟨# var_zero, # var_zero⟩)
        (⟨π₁ (# var_zero), π₂ (# var_zero)⟩)))).

End Residuals.
