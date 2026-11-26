From Cats.STLC Require Import NormalizationComparison.
From Cats Require Import
  STLC.Set
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Contraction Comparison Universe Regressions

    Keep the path bound independent of world-law classification. A chosen
    normalization isomorphism is sufficient; no semantic bound is forced
    into the comparison API. *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Paths below World Laws

    Fix [b < r < e < p < l]. The path need not contain the larger world
    law bound. Both endpoints use the same selected inverse. *)

Section SmallPaths.
Universes b r e p l.
Constraint b < r, r < e, e < p, p < l.
Context {B : Type@{b}} (A : Ty B).
Context (I : (NfEmbedN A) ⦂
    (NfPsh A : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{b e _ _ _ _ _}) ≅N TmRenamingPsh A).

(** Neither endpoint's irreducibility is needed for agreement. *)

Definition small_path_long_comparison {Γ : Ctx B} {t u v : Tm Γ A}
    (h : ReflTransClos@{b e p} BetaEtaContractStep@{b e l} t u)
    (k : ReflTransClos@{b e p} BetaEtaContractStep@{b e l} t v)
  : ContractionLongN A I Γ u = ContractionLongN A I Γ v
  := contraction_endpoints_long A I h k.

End SmallPaths.

(** ** Paths above World Laws

    Fix [b < e < r < l < p]. World hom equality may exceed equation
    witnesses; the comparison also supports paths above world laws. *)

Section LargePaths.
Universes b e r l p.
Constraint b < e, e < r, r < l, l < p.
Context {B : Type@{b}} (A : Ty B).
Context (I : (NfEmbedN A) ⦂
    (NfPsh A : Fct ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{b e _ _ _ _ _}) ≅N TmRenamingPsh A).

(** Irreducibility certificates and paths retain their own bounds. *)

Definition large_path_short_comparison {Γ : Ctx B} (t : Tm Γ A)
    (s : ShortForm Γ A)
    (h : ReflTransClos@{b e p} BetaEtaContractStep@{b e l} t s.1)
  : ContractionLongN A I Γ t = short_to_long A I s
  := short_endpoint_comparison A I t s h.

End LargePaths.

(** ** The Constructed Normalizer

    The general comparison accepts the actual normalization isomorphism.
    This checks the connection to the executable algorithm. *)

Section ActualNormalizer.
Context {B : Type}.

(** The chosen inverse of the constructed isomorphism computes as NbE. *)

Definition constructed_comparison_computes {Γ : Ctx B} {A : Ty B}
    (t : Tm Γ A)
  : ContractionLongN A (NormalFormsIsoN A).2 Γ t = nf t
  := eq_refl.

End ActualNormalizer.
