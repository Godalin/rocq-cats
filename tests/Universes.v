From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Bicategory Cat.ThinBicat.
From Cats Require Import Cat.CCC.
From Cats Require Import DTT.CwF DTT.Context.Extension DTT.Context.Conversion.
From Cats Require Import DTT.Context.Representation.
From Cats Require Import DTT.Display DTT.Context.Display.
From Cats Require Import DTT.Context.Pullback.
From Cats Require Import DTT.Comprehension.
From Cats Require Import Cat.Arrow Cat.Section DTT.Context.Section.
From Cats Require Import Cat.ArrowFibration.
From Cats Require Import Cat.SliceArrow.
From Cats Require Import Cat.Pullback Instance.Set.Core Instance.Set.Pullback.
From Cats Require Import Instance.Set.Fam.Slice Instance.Set.Fam.SliceReindex.
From Cats Require Import Instance.Set.Fam.Core Instance.Set.Fam.Cat Instance.Set.CwF.

(** Basic sets and their category accept both carrier/equality orderings. *)
Section SetLevels.
Universe u p.
Constraint Set < u.
Constraint u < p.
Context (X : SetC@{u p}) (Y : SetC@{p u}).

Definition high_eq_set_id : X →r X := id_resp.
Definition low_eq_set_id : Y →r Y := id_resp.
Definition high_eq_sets := SetCat@{u p _ _ _ _ _}.
Definition low_eq_sets := SetCat@{p u _ _ _ _ _}.
End SetLevels.

(** Guard against identifying morphism and equivalence-witness universes
    when a construction instantiates a bare [Cat]. Test both orderings. *)
Section CategoryLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p <= l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).

Definition high_eq_hom (X Y : @Ob C) : SetC@{h p} := HomSet X Y.
Definition low_eq_hom (X Y : @Ob D) : SetC@{p h} := HomSet X Y.
Definition high_eq_id := @IdF C.
Definition low_eq_id := @IdF D.
Definition high_eq_product := C ×C C.
Definition low_eq_product := D ×C D.
Definition high_eq_functors := Fct C C.
Definition low_eq_functors := Fct D D.
Definition high_eq_ccc := CCC C.
Definition low_eq_ccc := CCC D.
Definition high_eq_cwf := CwF C.
Definition low_eq_cwf := CwF D.
Definition high_eq_arrow_hom (X Y : ArrowOb C) : SetC@{p p}
  := @HomSet (Arr C) X Y.
Definition low_eq_arrow_hom (X Y : ArrowOb D) : SetC@{p h}
  := @HomSet (Arr D) X Y.
Definition high_eq_sections (X Y : @Ob C) (f : Hom X Y) : SetC@{p p} := Sec(f).
Definition low_eq_sections (X Y : @Ob D) (f : Hom X Y) : SetC@{p h} := Sec(f).
Definition high_eq_arrow_cartesian := @arrow_cartesian_iff_pullback C.
Definition low_eq_arrow_cartesian := @arrow_cartesian_iff_pullback D.
Definition high_eq_arrow_lifts := pullbacks_iff_arrow_cartesian_lifts C.
Definition low_eq_arrow_lifts := pullbacks_iff_arrow_cartesian_lifts D.
Definition high_eq_slice_arrow_faithful := @slice_arrow_faithful C.
Definition low_eq_slice_arrow_faithful := @slice_arrow_faithful D.
Definition high_eq_slice_codomain_reindex := @SliceReindexSquareN C.
Definition low_eq_slice_codomain_reindex := @SliceReindexSquareN D.
Definition high_eq_slice_codomain_comp := @slice_reindex_comp_cartesian_factor C.
Definition low_eq_slice_codomain_comp := @slice_reindex_comp_cartesian_factor D.
Definition high_eq_thin : Bicat@{o h p Set _ _ _} := ThinBicat C.
Definition low_eq_thin := ThinBicat D.
End CategoryLevels.

(** The same hom-category must retain distinct 1-cell, 2-cell and
    2-cell-equivalence levels through the bicategory projections. *)
Section BicategoryLevels.
Universe o h t p a b l.
Constraint o < h.
Constraint h < t.
Constraint t < p.
Constraint p < a.
Constraint a <= b.
Constraint p <= l.
Context (K : Bicat@{o h t p a b l}) (L : Bicat@{o h p t a b l}).

Definition independent_hom (X Y : ObB K) : Cat@{h t p l l} := HomCat X Y.
Definition independent_hom_reverse (X Y : ObB L) : Cat@{h p t l l} := HomCat X Y.
Definition independent_cells (X Y : ObB K) : Type@{h} := Cell1 X Y.
End BicategoryLevels.

(** The chosen pullback instance formerly collapsed these two levels. *)
Section SetoidPullbackLevels.
Universe u p.
Constraint p < u.
Context (X Y : SetC@{u p}) (f : X →r Y).
Definition distinct_setoid_pullbacks : HasPullback (SetCat@{u p _ _ _ _ _})
  := SetCat_HasPullback.
Definition distinct_sum_reindex := fam_sum_reindex_nat_iso f.
Definition distinct_fam_slice_equivalence := fam_slice_equiv X.
End SetoidPullbackLevels.

(** Codes can be larger than contexts. Decoded fibers determine the two
    context levels, which remain independent in either ordering. *)
Section CodeModelLevels.
Universe u p c q l.
Constraint Set < u.
Constraint u < p.
Constraint p < c.
Constraint c < q.
Constraint q < l.
Context (Code : SetC@{c q}) (Code' : SetC@{q c}).
Context (El : FamS@{c q l u p} Code) (El' : FamS@{c q l p u} Code).
Context (El'' : FamS@{q c l u p} Code').

Definition high_eq_code_model : CwF (SetCat@{u p _ _ _ _ _}) := SetCwF El.
Definition low_eq_code_model : CwF (SetCat@{p u _ _ _ _ _}) := SetCwF El'.
Definition reverse_code_model : CwF (SetCat@{u p _ _ _ _ _}) := SetCwF El''.
End CodeModelLevels.

(** Representation must not identify hom, term or equality-witness levels. *)
Section ContextRepresentationLevels.
Universe o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Functor (C^op) FamCat) (U : Functor (D^op) FamCat).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).

Definition high_eq_rep_types (Γ : @Ob C) : SetC@{a c} := Ty T Γ.
Definition high_eq_rep_terms (Γ : @Ob C) (A : Ty T Γ) : SetC@{b d} := Tm T Γ A.
Definition low_eq_rep_types (Γ : @Ob D) : SetC@{c a} := Ty U Γ.
Definition low_eq_rep_terms (Γ : @Ob D) (A : Ty U Γ) : SetC@{d b} := Tm U Γ A.
Definition high_eq_context_pairs (Γ Δ : @Ob C) (A : Ty T Γ) : SetC@{b d}
  := ContextPairS T A Δ.
Definition low_eq_context_pairs (Γ Δ : @Ob D) (A : Ty U Γ) : SetC@{d b}
  := ContextPairS U A Δ.
Definition high_eq_representation := @context_extension_nat_iso C T HC.
Definition low_eq_representation := @context_extension_nat_iso D U HU.
Definition high_eq_context_conversion := @context_conv_iso C T HC.
Definition low_eq_context_conversion := @context_conv_iso D U HU.
Definition high_eq_display_pullback := @context_lift_pullback C T HC.
Definition low_eq_display_pullback := @context_lift_pullback D U HU.
Definition high_eq_coherent_display : HasDisplay C (FamBaseF ∘F T)
  := @ContextExtension_HasDisplay C T HC.
Definition low_eq_coherent_display : HasDisplay D (FamBaseF ∘F U)
  := @ContextExtension_HasDisplay D U HU.
Definition high_eq_display_conversion := @display_conv_iso C (FamBaseF ∘F T)
  high_eq_coherent_display.
Definition low_eq_display_conversion := @display_conv_iso D (FamBaseF ∘F U)
  low_eq_coherent_display.
Definition high_eq_context_maps (X Y : ContextType T) : SetC@{p p}
  := @HomSet (ContextTypeCat T) X Y.
Definition low_eq_context_maps (X Y : ContextType U) : SetC@{p h}
  := @HomSet (ContextTypeCat U) X Y.
Definition high_eq_cwf_comprehension := @CwFComprehension C T HC.
Definition low_eq_cwf_comprehension := @CwFComprehension D U HU.
Definition high_eq_full_comprehension := @cwf_comprehension_fully_faithful C T HC.
Definition low_eq_full_comprehension := @cwf_comprehension_fully_faithful D U HU.
Definition high_eq_term_sections := @context_term_section_iso C T HC.
Definition low_eq_term_sections := @context_term_section_iso D U HU.
Definition high_eq_context_representations := @context_extension_iff_representation C T.
Definition low_eq_context_representations := @context_extension_iff_representation D U.
Definition high_eq_represented_cwf := @RepresentedCwF C T.
Definition low_eq_represented_cwf := @RepresentedCwF D U.
End ContextRepresentationLevels.
