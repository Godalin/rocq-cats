From Cats Require Import
  STLC.CategoricalGluing
  STLC.Set
  Cat.Core
  Cat.Natural
  Cat.Gluing.Core
  Cat.CCC.Core
  Cat.Exponential.Core
  Cat.Product.Core
  Cat.Functor.FiniteProducts
  Instance.Set.Core
  Instance.Set.Lift
  Instance.Set.Product
  Instance.Set.PresheafExponential.

(** * Categorical Normalization Interfaces

    Check the new squares at two opposite orders of the original semantic
    and equation bounds. Separately instantiate the explicitly chosen CCC
    at its sufficient common value bound. Concrete reductions must retain
    the original normalizer and the unchanged syntax component. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Larger Semantics and Smaller Ambient Equality

    Keep [b < r < e < s < p < u < l]. Observe both original projections
    from one evaluated categorical object; they cannot silently share a
    semantic/equation bound or a common ambient carrier/equality bound. *)

Section LargeSemantics.
Universes b r e s p u l.
Constraint b < r, r < e, e < s, s < p, p < u, u < l.
Context {B : Type@{b}}.

(** Both retained values come from the left component of one new square. *)

Definition categorical_separated_values (A : Ty B) (Γ : Ctx B)
    (t : Tm Γ A)
  : (LiftS@{b e u p} (TmS@{b e} Γ A) *
      LiftS@{s s u p} ((SemF A : Fct
        ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{s s _ _ _ _ _}) Γ))%type
  := let x := comma_left (CategoricalEvaluationM A) Γ {|lower := t
                                                      |} in
      (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

(** The categorical comparison accepts the same ambient strict order. *)

Definition categorical_separated_comparison (A : Ty B)
  : @HomEq (Gluing (@IdF (FctCat
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _}))) _ _
      (CategoricalQuoteM A ∘ CategoricalEvaluationM A)
      (CategoricalNormalizeM A)
  := categorical_evaluation_quote A.

(** Compare the complete respectful projections of the categorical
    object's domain, including the original equation and semantic
    relations. This catches wrappers that only preserve carrier values. *)

Definition categorical_separated_projection_arrows (A : Ty B) (Γ : Ctx B)
  : let R : Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _} :=
        comma_left_ob (NormalizationRelationOb A) in
    ((R Γ →r LiftS@{b e u p} (TmS@{b e} Γ A)) *
     (R Γ →r LiftS@{s s u p} ((SemF A : Fct
       ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ)))%type
  := (GluingSyntaxN A Γ, GluingValuesN A Γ).

End LargeSemantics.

(** ** Larger Equations and Larger Ambient Equality

    Reverse to [b < r < l < s < e < u < p]. World laws are now below
    semantics, and ambient equality is above the carrier. *)

Section LargeEquations.
Universes b r l s e u p.
Constraint b < r, r < l, l < s, s < e, e < u, u < p.
Context {B : Type@{b}}.

(** The same paired observation retains the opposite native bounds. *)

Definition categorical_reversed_values (A : Ty B) (Γ : Ctx B)
    (t : Tm Γ A)
  : (LiftS@{b e u p} (TmS@{b e} Γ A) *
      LiftS@{s s u p} ((SemF A : Fct
        ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{s s _ _ _ _ _}) Γ))%type
  := let x := comma_left (CategoricalEvaluationM A) Γ {|lower := t
                                                      |} in
      (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

(** The inverse also exists at this larger equality bound. *)

Definition categorical_reversed_inverse (A : Ty B)
  : @is_iso (Gluing (@IdF (FctCat
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _}))) _ _ (CategoricalNormalizeM A)
  := categorical_normalization_iso A.

(** Compare the complete respectful projections of the categorical
    object's domain, including the original equation and semantic
    relations. This catches wrappers that only preserve carrier values. *)

Definition categorical_reversed_projection_arrows (A : Ty B) (Γ : Ctx B)
  : let R : Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _} :=
        comma_left_ob (NormalizationRelationOb A) in
    ((R Γ →r LiftS@{b e u p} (TmS@{b e} Γ A)) *
     (R Γ →r LiftS@{s s u p} ((SemF A : Fct
       ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ)))%type
  := (GluingSyntaxN A Γ, GluingValuesN A Γ).

End LargeEquations.

(** ** Chosen Structures with Larger World Laws

    Only the CCC wrapper uses a common value/equality bound. Its world
    laws may still exceed that bound: [b < r < u < l]. *)

Section LargeWorldLaws.
Universes b r u l.
Constraint b < r, r < u, u < l.
Context (B : Type@{b}).

(** Instantiate the full arrow-category CCC at the native world levels. *)

Definition categorical_large_law_ccc
  : CCC
  := RenamingGluing_CCC B.

(** The complete bundle retains the original category at these native bounds. *)

Example categorical_large_law_ccc_category
  : (RenamingGluing_CCC B : Cat) = Gluing (@IdF (FctCat
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u u _ _ _ _ _})).
Proof. reflexivity. Qed.

(** Application compares with the selected evaluation at these bounds. *)

Definition categorical_large_law_application (A U : Ty B)
  : SemanticApplyN A U ≈N
      (@Cats.Cat.Exponential.Core.eval (FctCat
        ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{u u _ _ _ _ _})
        (@FctCat_HasProduct _ _ SetCat_HasProduct)
        (Psh_HasExponential (RenamingCat B)) (SemF A) (SemF U))
  := semantic_application_eval A U.

End LargeWorldLaws.

(** ** Chosen Structures with Smaller World Laws

    Reverse the world Hom/equality and law/value orders to [r < b < l < u].
    The semantic operation comparisons must use the same world and value
    bounds as that CCC. *)

Section SmallWorldLaws.
Universes b r l u.
Constraint r < b, b < l, l < u.
Context (B : Type@{b}).

(** The reverse strict order also instantiates the complete structure. *)

Definition categorical_small_law_ccc
  : CCC
  := RenamingGluing_CCC B.

(** The complete bundle retains the original category at these native bounds. *)

Example categorical_small_law_ccc_category
  : (RenamingGluing_CCC B : Cat) = Gluing (@IdF (FctCat
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u u _ _ _ _ _})).
Proof. reflexivity. Qed.

(** The natural isomorphism uses the same selected exponential object. *)

Definition categorical_small_law_arrow (A U : Ty B)
  : SemF (A ⇒ U) ≅N
      (@exp (FctCat ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{u u _ _ _ _ _})
        (@FctCat_HasProduct _ _ SetCat_HasProduct)
        (Psh_HasExponential (RenamingCat B)) (SemF U) (SemF A))
  := SemanticArrowIsoN A U.

(** Transposition comparison accepts an arbitrary body natural map. *)

Definition categorical_small_law_curry (A U : Ty B)
    (H : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{u u _ _ _ _ _})
    (α : PointwiseProductF H (SemF A) ⇒ SemF U)
  : SemanticCurryN A U H α ≈N
      (@Cats.Cat.Exponential.Core.curry (FctCat
        ((RenamingCat B : Cat@{b b r l l})^op)
          SetCat@{u u _ _ _ _ _})
        (@FctCat_HasProduct _ _ SetCat_HasProduct)
        (Psh_HasExponential (RenamingCat B)) (SemF A) (SemF U) H α)
  := semantic_abstraction_curry A U H α.

(** The normalization isomorphism inhabits this same explicitly selected
    CCC; no separate choice or reconstructed category is needed. *)

Definition categorical_selected_normalization_iso (A : Ty B)
  : @is_iso (RenamingGluing_CCC B : Cat) _ _
      (CategoricalNormalizeM A)
  := categorical_normalization_iso A.

End SmallWorldLaws.

(** ** Original Computation under the Squares

    A base-labelled identity abstraction tests the function case, without
    deciding labels. Both squares and their composite keep the original
    executable NbE and identity syntax maps. *)

Section Computations.
Context {B : Type} (a : B).

(** A closed identity at an arbitrary base label. *)

Definition categorical_identity_term
  : Tm (ctx_empty : Ctx B) (ty_base a ⇒ ty_base a)
  := tm_lam (tm_var var_zero).

(** The normalizing square computes the old long normal form natively. *)

Example categorical_normalize_computes
  : lower (comma_left (CategoricalNormalizeM _) ctx_empty
      {|lower := categorical_identity_term
      |}) = nf_lam (nf_base (ne_var var_zero)).
Proof. reflexivity. Defined.

(** Factoring through the realized pair computes exactly the same tree. *)

Example categorical_evaluation_quote_computes
  : lower (comma_left (CategoricalQuoteM _ ∘ CategoricalEvaluationM _)
      ctx_empty {|lower := categorical_identity_term
                |}) = nf_lam (nf_base (ne_var var_zero)).
Proof. reflexivity. Defined.

(** The composite's base component retains the actual input term. *)

Example categorical_base_computes
  : lower (comma_right (CategoricalQuoteM _ ∘ CategoricalEvaluationM _)
      ctx_empty {|lower := categorical_identity_term
                |}) = categorical_identity_term.
Proof. reflexivity. Defined.

(** The chosen inverse is the original normal-form embedding. *)

Example categorical_inverse_computes
  : lower (comma_left (categorical_normalization_iso
      (ty_base a ⇒ ty_base a)).1 ctx_empty
      {|lower := nf_lam (nf_base (ne_var var_zero))
      |}) = categorical_identity_term.
Proof. reflexivity. Defined.

(** A beta redex with a free input tests open evaluation. *)

Definition categorical_open_redex
  : Tm ((ctx_empty : Ctx B) ▻ ty_base a) (ty_base a)
  := tm_app (tm_lam (tm_var var_zero)) (tm_var var_zero).

(** Quotation of the lifted realized value removes this redex natively. *)

Example categorical_open_beta_computes
  : lower (comma_left (CategoricalQuoteM _ ∘ CategoricalEvaluationM _)
      _ {|lower := categorical_open_redex
         |}) = nf_base (ne_var var_zero).
Proof. reflexivity. Defined.

(** Restrict the output along a genuine weakening; the variable moves to
    the older position, so this is not an identity-world computation. *)

Example categorical_weakening_computes
  : lower (fmap (comma_left_ob (NormalizationNormalOb (ty_base a)))
      (@ren_weaken B (ctx_empty ▻ ty_base a) (ty_base a))
      (comma_left (CategoricalQuoteM _ ∘ CategoricalEvaluationM _)
        _ {|lower := categorical_open_redex
           |})) = nf_base (ne_var (var_succ var_zero)).
Proof. reflexivity. Defined.

End Computations.
