From Cats.STLC Require Import Gluing.
From Cats Require Import
  STLC.Set
  Instance.Set.Core
  Instance.Set.Lift.

(** * Normalization Gluing Regressions

    Both projections of one glued value must retain independently chosen
    syntax/equation and semantic bounds. Check the two orders, world laws
    above and below semantics, and equal computational levels. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Semantics above Equations

    Fix [b < r < e < s < p < u < l]. Stored values and equation witnesses
    must remain independent; world laws may exceed the glued carrier. *)

Section LargeSemantics.
Universes b r e s p u l.
Constraint b < r, r < e, e < s, s < p, p < u, u < l.
Context {B : Type@{b}}.

(** One input simultaneously determines both projection bounds. *)

Definition separated_gluing_projections (A : Ty B) (Γ : Ctx B)
    (x : (NormalizationGluingF A : Fct
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _}) Γ)
  : (LiftS@{b e u p} (TmS@{b e} Γ A) *
      LiftS@{s s u p} ((SemF A : Fct
        ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ))%type
  := (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

(** Compare the full respectful projection arrows, including their
    domain and codomain equality relations. Merely observing carrier
    values would not detect a collapsed internal equation universe. *)

Definition separated_gluing_projection_arrows (A : Ty B) (Γ : Ctx B)
  : let R : Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _} := NormalizationGluingF A in
    ((R Γ →r LiftS@{b e u p} (TmS@{b e} Γ A)) *
     (R Γ →r LiftS@{s s u p} ((SemF A : Fct
       ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ)))%type
  := (GluingSyntaxN A Γ, GluingValuesN A Γ).

End LargeSemantics.

(** ** Equations above Semantics

    Fix [b < r < l < s < e < u < p]. Equality and semantics are reversed;
    semantic values exceed world laws, while ambient equality exceeds
    the glued carrier. *)

Section LargeEquations.
Universes b r l s e u p.
Constraint b < r, r < l, l < s, s < e, e < u, u < p.
Context {B : Type@{b}}.

(** The same interface supports the opposite ordering. *)

Definition reversed_gluing_projections (A : Ty B) (Γ : Ctx B)
    (x : (NormalizationGluingF A : Fct
      ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _}) Γ)
  : (LiftS@{b e u p} (TmS@{b e} Γ A) *
      LiftS@{s s u p} ((SemF A : Fct
        ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ))%type
  := (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

(** Compare the full respectful projection arrows, including their
    domain and codomain equality relations. Merely observing carrier
    values would not detect a collapsed internal equation universe. *)

Definition reversed_gluing_projection_arrows (A : Ty B) (Γ : Ctx B)
  : let R : Fct ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{u p _ _ _ _ _} := NormalizationGluingF A in
    ((R Γ →r LiftS@{b e u p} (TmS@{b e} Γ A)) *
     (R Γ →r LiftS@{s s u p} ((SemF A : Fct
       ((RenamingCat B)^op) SetCat@{s s _ _ _ _ _}) Γ)))%type
  := (GluingSyntaxN A Γ, GluingValuesN A Γ).

End LargeEquations.

(** ** Equal Computational Bounds

    Syntax, semantics, evidence and glued values may share [b]. Only the
    auxiliary world-law bound is strictly larger. *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}}.

(** No strict separation is required by the gluing construction. *)

Definition equal_gluing_projections (A : Ty B) (Γ : Ctx B)
    (x : (NormalizationGluingF A : Fct
      ((RenamingCat B : Cat@{b b b l l})^op)
        SetCat@{b b _ _ _ _ _}) Γ)
  : (LiftS@{b b b b} (TmS@{b b} Γ A) *
      LiftS@{b b b b} ((SemF A : Fct
        ((RenamingCat B)^op) SetCat@{b b _ _ _ _ _}) Γ))%type
  := (GluingSyntaxN A Γ x, GluingValuesN A Γ x).

End EqualLevels.

(** ** Executable Recovery of Normal Forms

    Fix a signature and a base label. Normal forms supplied directly,
    rather than through a prior normalization call, satisfy the retraction.
    The gluing quote of a reflected base neutral is its normal wrapper. *)

Section Computations.
Context {B : Type} (a : B).

(** The retraction applies to any supplied long normal form. *)

Definition supplied_normal_retract {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
  : nf (embed_nf v) = v
  := nf_embed_nf v.

(** A neutral identity abstraction is already a long normal form. *)

Example normal_identity_computes
  : nf (embed_nf (nf_lam (nf_base
      (ne_var (var_zero : Var ((ctx_empty : Ctx B) ▻ ty_base a)
        (ty_base a)))))) = nf_lam (nf_base (ne_var var_zero)).
Proof. reflexivity. Defined.

End Computations.
