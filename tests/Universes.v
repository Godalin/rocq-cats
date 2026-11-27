From Cats Require Import
  Instance.Set.Simplicial.Vertex.Reconstruction
  Instance.Set.Simplicial.Vertex.Kan
  STLC.Inhabitation
  STLC.Free.
From Cats Require Import
  Cat.Shape.Simplex.Core
  Instance.Set.Simplicial.Nerve
  Instance.Set.Simplicial.Monoid
  Instance.Set.Simplicial.Vertex.Spine
  Instance.Set.Simplicial.Vertex.Horn2
  Instance.Set.Lift.
From Cats Require Import
  Cat.Groupoid.Core
  Cat.Groupoid.Functor
  Instance.Set.Groupoid.
From Cats Require Import
  Cat.Slice.Core
  Instance.Set.Fam.Fixed
  Instance.Set.Fam.Groupoid
  Instance.Set.Fam.GroupoidSlice.
From Cats Require Import
  Algebra.Group.Category
  Algebra.Monoid.Action.

From Cats Require Import
  Cat.Core
  Cat.CatCat
  Cat.Functor.Core
  Cat.CCC.Functor
  Cat.Natural
  Cat.Bicategory.Core
  Cat.Bicategory.Thin.
From Cats Require Import Cat.CCC.Core.
From Cats Require Import
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Instance.Set.ExponentialHom.
From Cats Require Import
  Cat.Adjunction
  Instance.Set.Adjunction.
From Cats Require Import
  Cat.Diagram.Core
  Cat.Limit.Core
  Cat.Limit.Adjunction
  Cat.Limit.Preservation.
From Cats Require Import
  Cat.Diagram.Dual
  Cat.Colimit.Core
  Cat.Colimit.Adjunction
  Cat.Colimit.Preservation.
From Cats Require Import
  Cat.Coproduct.Core
  Cat.Coequalizer
  Cat.Colimit.Initial
  Cat.Colimit.Coproduct
  Cat.Colimit.Coequalizer
  Cat.Pushout
  Cat.Colimit.Pushout
  Cat.Colimit.Finite
  Cat.Colimit.Construction
  Cat.Colimit.Graph.Finite
  Cat.Colimit.Reindex
  Cat.Colimit.Transport.
From Cats Require Import
  Graph.Morphism
  Graph.Path
  Cat.Free
  Cat.Diagram.Shape.
From Cats Require Import
  Cat.Limit.Product
  Cat.Limit.Pullback.
From Cats Require Import
  Cat.Terminal
  Cat.Equalizer
  Cat.Limit.Terminal
  Cat.Limit.Equalizer.
From Cats Require Import Cat.Limit.Finite.
From Cats Require Import
  Cat.Product.Indexed
  Cat.Limit.Construction.
From Cats Require Import Cat.Product.Finite.
From Cats Require Import Cat.Limit.Graph.Finite.
From Cats Require Import
  Cat.Diagram.Reindex
  Cat.Diagram.Presheaf
  Cat.Limit.Reindex.
From Cats Require Import
  DTT.CwF
  DTT.Context.Extension
  DTT.Context.Conversion.
From Cats Require Import DTT.Context.Representation.
From Cats Require Import
  DTT.Display.Core
  DTT.Context.Display.
From Cats Require Import
  DTT.Display.Section
  DTT.Display.Representation
  DTT.Display.Comprehension
  Instance.Set.Elements
  Cat.Fibration
  Cat.Comprehension.
From Cats Require Import DTT.Context.Pullback.
From Cats Require Import DTT.Comprehension.
From Cats Require Import
  Cat.Arrow.Core
  Cat.Section
  DTT.Context.Section.
From Cats Require Import Cat.Arrow.Fibration.
From Cats Require Import Cat.Slice.Arrow.
From Cats Require Import
  Cat.Pullback
  Instance.Set.Core
  Instance.Set.Pullback.
From Cats Require Import
  Instance.Set.Fam.Slice
  Instance.Set.Fam.SliceReindex.
From Cats Require Import
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  Instance.Set.CwF.
From Cats Require Import
  Instance.Set.Yoneda
  Instance.Set.Representable.
From Cats Require Import
  Instance.Set.Coproduct
  Instance.Set.Coequalizer
  Instance.Set.Equalizer
  Instance.Set.Limit
  Instance.Set.Colimit
  Instance.Set.Pushout.
From Cats Require Import
  Cat.Exponential.Laws
  Cat.Exponential.InternalHom
  Cat.Limit.Exponential
  Instance.Set.Product
  Instance.Set.ProductHom.

(** Concrete setoid models retain independent levels where possible. The
    chosen equalizers need [p ≤ u], while generated coequalizers need [u ≤ p].
    These bounds belong to these models, not the abstract interfaces. *)

Section ConcreteSetModelLevels.
Universes u p s.
Constraint Set < u.
Constraint u < p.
Constraint p < s.

Definition high_eq_set_coproducts
  : HasCoproduct (SetCat@{u p _ _ _ _ _})
  := SetCat_HasCoproduct.
Definition low_eq_set_coproducts
  : HasCoproduct (SetCat@{p u _ _ _ _ _})
  := SetCat_HasCoproduct.

Definition high_eq_set_finite_products (n : nat)
  : HasLimitsOfShape (SetCat@{u p _ _ _ _ _}) (DiscreteCat (Fin n))
  := SetCat_FiniteProductLimits n.
Definition low_eq_set_finite_products (n : nat)
  : HasLimitsOfShape (SetCat@{p u _ _ _ _ _}) (DiscreteCat (Fin n))
  := SetCat_FiniteProductLimits n.
Definition high_eq_set_finite_coproducts (n : nat)
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) (DiscreteCat (Fin n))
  := SetCat_FiniteCoproductColimits n.
Definition low_eq_set_finite_coproducts (n : nat)
  : HasColimitsOfShape (SetCat@{p u _ _ _ _ _}) (DiscreteCat (Fin n))
  := SetCat_FiniteCoproductColimits n.

Definition high_eq_set_pushouts
  : HasPushout (SetCat@{u p _ _ _ _ _})
  := SetCat_HasPushout.
Definition low_eq_set_equalizers
  : HasEqualizer (SetCat@{p u _ _ _ _ _})
  := SetCat_HasEqualizer.

Fail Definition incompatible_set_coequalizers
  : HasCoequalizer (SetCat@{p u _ _ _ _ _})
  := SetCat_HasCoequalizer.
Fail Definition incompatible_set_equalizers
  : HasEqualizer (SetCat@{u p _ _ _ _ _})
  := SetCat_HasEqualizer.

Context (J : Cat@{u u s _ _}) (G : Graph@{u u s}).

(** Large relation witnesses in the shape do not enlarge the indexing
    carrier required by either model. *)

Definition high_eq_set_diagram_colimits
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) J
  := SetCat_HasColimitsOfShape J.
Definition low_eq_set_diagram_limits
  : HasLimitsOfShape (SetCat@{p u _ _ _ _ _}) J
  := SetCat_HasLimitsOfShape J.
Definition high_eq_set_graph_colimits
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) (FreeCat G)
  := SetCat_GraphColimits G.
Definition low_eq_set_graph_limits
  : HasLimitsOfShape (SetCat@{p u _ _ _ _ _}) (FreeCat G)
  := SetCat_GraphLimits G.

Context (K : Cat@{s s s _ _}) (HK : HasFiniteHomCover K)
    (HG : HasFiniteGen K).

(** Finite covers and generators bypass the larger raw shape carriers. *)

Definition high_eq_set_finite_colimits
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) K
  := @SetCat_FiniteColimits K HK.
Definition low_eq_set_finite_limits
  : HasLimitsOfShape (SetCat@{p u _ _ _ _ _}) K
  := @SetCat_FiniteLimits K HK.
Definition high_eq_set_generated_colimits
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) K
  := @SetCat_GeneratedColimits K HG.
Definition low_eq_set_generated_limits
  : HasLimitsOfShape (SetCat@{p u _ _ _ _ _}) K
  := @SetCat_GeneratedLimits K HG.
End ConcreteSetModelLevels.

(** Basic sets and their category accept both carrier/equality orderings. *)

Section SetLevels.
Universe u p.
Constraint Set < u.
Constraint u < p.
Context (X : SetC@{u p}) (Y : SetC@{p u}).

Definition high_eq_set_id
  : X →r X
  := id_resp.
Definition low_eq_set_id
  : Y →r Y
  := id_resp.
Definition high_eq_sets
  := SetCat@{u p _ _ _ _ _}.
Definition low_eq_sets
  := SetCat@{p u _ _ _ _ _}.
Definition high_eq_finite_positions (n : nat)
  : SetC@{u p}
  := FinS n.
Definition low_eq_finite_positions (n : nat)
  : SetC@{p u}
  := FinS n.
Definition high_eq_finite_cover (n : nat)
  : HasFiniteCover (FinS@{u p _} n)
  := FinitePositionsCover n.
Definition low_eq_finite_cover (n : nat)
  : HasFiniteCover (FinS@{p u _} n)
  := FinitePositionsCover n.
End SetLevels.

(** Guard against identifying morphism and equivalence-witness universes
    when a construction instantiates a bare [Cat]. Test both orderings. *)

Section CategoryLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p <= l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).

Definition high_eq_hom (X Y : @Ob C)
  : SetC@{h p}
  := HomSet X Y.
Definition low_eq_hom (X Y : @Ob D)
  : SetC@{p h}
  := HomSet X Y.
Definition high_eq_id
  := @IdF C.
Definition low_eq_id
  := @IdF D.
Definition high_eq_product
  := C ×C C.
Definition low_eq_product
  := D ×C D.
Definition high_eq_functors
  := FctCat C C.
Definition low_eq_functors
  := FctCat D D.
Definition high_eq_ccc (HT : HasTerminal C) (HP : HasProduct C)
    (HE : HasExponential HP)
  : CCC@{o h p l l}
  := CCCOfCartCat (MakeCartCat C HT HP) HE.
Definition low_eq_ccc (HT : HasTerminal D) (HP : HasProduct D)
    (HE : HasExponential HP)
  : CCC@{o p h l l}
  := CCCOfCartCat (MakeCartCat D HT HP) HE.
Definition high_eq_cwf
  := CwF C.
Definition low_eq_cwf
  := CwF D.
Definition high_eq_arrow_hom (X Y : ArrowOb C)
  : SetC@{p p}
  := @HomSet (Arr C) X Y.
Definition low_eq_arrow_hom (X Y : ArrowOb D)
  : SetC@{p h}
  := @HomSet (Arr D) X Y.
Definition high_eq_sections (X Y : @Ob C) (f : Hom X Y)
  : SetC@{p p}
  := Sec(f).
Definition low_eq_sections (X Y : @Ob D) (f : Hom X Y)
  : SetC@{p h}
  := Sec(f).
Definition high_eq_arrow_cartesian
  := @arrow_cartesian_iff_pullback C.
Definition low_eq_arrow_cartesian
  := @arrow_cartesian_iff_pullback D.
Definition high_eq_arrow_lifts
  := pullbacks_iff_arrow_cartesian_lifts C.
Definition low_eq_arrow_lifts
  := pullbacks_iff_arrow_cartesian_lifts D.
Definition high_eq_slice_arrow_faithful
  := @slice_arrow_faithful C.
Definition low_eq_slice_arrow_faithful
  := @slice_arrow_faithful D.
Definition high_eq_slice_codomain_reindex
  := @SliceReindexSquareN C.
Definition low_eq_slice_codomain_reindex
  := @SliceReindexSquareN D.
Definition high_eq_slice_codomain_comp
  := @slice_reindex_comp_cartesian_factor C.
Definition low_eq_slice_codomain_comp
  := @slice_reindex_comp_cartesian_factor D.
Definition high_eq_thin
  : Bicat@{o h p Set _ _ _}
  := ThinBicat C.
Definition low_eq_thin
  := ThinBicat D.
(** A CCC can retain terminal evidence above its category law bound. *)

Universe t.
Constraint l < t.
Example larger_terminal_witness (HT : HasTerminal@{o h p l t} C)
    (HP : HasProduct C) (HE : HasExponential HP)
  : Cartesian.Core.hasTerminal
      (CCCOfCartCat (MakeCartCat C HT HP) HE : CCC@{o h p l t}) = HT
  := eq_refl.

End CategoryLevels.

(** Transposition must preserve hom/equality levels in either ordering.
    The ambient set category for the correspondence must not identify them. *)

Section ExponentialLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Context (C : CCC@{o h p l l}) (D : CCC@{o p h l l}).

Definition high_eq_curry (X Y Z : @Ob C)
  : HomSet (Z × X) Y →r HomSet Z (Y ^ X)
  := exp_curry_resp.
Definition low_eq_curry (X Y Z : @Ob D)
  : HomSet (Z × X) Y →r HomSet Z (Y ^ X)
  := exp_curry_resp.
Definition high_eq_uncurry (X Y Z : @Ob C)
  : HomSet Z (Y ^ X) →r HomSet (Z × X) Y
  := exp_uncurry_resp.
Definition low_eq_uncurry (X Y Z : @Ob D)
  : HomSet Z (Y ^ X) →r HomSet (Z × X) Y
  := exp_uncurry_resp.
Definition high_eq_exp_hom (X Y Z : @Ob C)
  : HomSet (Z × X) Y ≅[SetCat@{h p _ _ _ _ _}] HomSet Z (Y ^ X)
  := exp_hom_iso.
Definition low_eq_exp_hom (X Y Z : @Ob D)
  : HomSet (Z × X) Y ≅[SetCat@{p h _ _ _ _ _}] HomSet Z (Y ^ X)
  := exp_hom_iso.
Definition high_eq_exp_adj (X : @Ob C)
  : (-× X) ⊣ (-^ X)
  := ProdExpAdj X.
Definition low_eq_exp_adj (X : @Ob D)
  : (-× X) ⊣ (-^ X)
  := ProdExpAdj X.
Definition high_eq_exp_nat (X : @Ob C)
  : @NatIso _ SetCat@{h p _ _ _ _ _} (LeftHomF (-× X)) (RightHomF (-^ X))
  := exp_hom_nat_iso X.
Definition low_eq_exp_nat (X : @Ob D)
  : @NatIso _ SetCat@{p h _ _ _ _ _} (LeftHomF (-× X)) (RightHomF (-^ X))
  := exp_hom_nat_iso X.
Definition high_eq_exp_bifunctor
  : Fct ((C^op) ×C C) C
  := (-^-).
Definition low_eq_exp_bifunctor
  : Fct ((D^op) ×C D) D
  := (-^-).
Definition high_eq_contravariant_exp (Y : @Ob C)
  : Fct (C^op) C
  := (Y ^-).
Definition low_eq_contravariant_exp (Y : @Ob D)
  : Fct (D^op) D
  := (Y ^-).
Definition high_eq_fixed_exp (X : @Ob C)
  : AtLF (-^-) X ≅N (-^ X)
  := exp_fixed_nat_iso X.
Definition low_eq_fixed_exp (X : @Ob D)
  : AtLF (-^-) X ≅N (-^ X)
  := exp_fixed_nat_iso X.
(** Structural isomorphisms keep the two hom/equality orderings distinct. *)

Definition high_eq_exp_laws (X Y Z : @Ob C)
  : (((X × Y) ^ Z) ≅ ((X ^ Z) × (Y ^ Z))) ∧
      (((Y ^ X) ^ Z) ≅ (Y ^ (X × Z))) ∧ ((Y ^ 1) ≅ Y) ∧ ((1 ^ X) ≅ 1)
  := (exp_product_iso Z X Y,
      (exp_iterated_iso X Z Y,
        (exp_unit_iso Y, exp_terminal_iso X))).
Definition low_eq_exp_laws (X Y Z : @Ob D)
  : (((X × Y) ^ Z) ≅ ((X ^ Z) × (Y ^ Z))) ∧
      (((Y ^ X) ^ Z) ≅ (Y ^ (X × Z))) ∧ ((Y ^ 1) ≅ Y) ∧ ((1 ^ X) ≅ 1)
  := (exp_product_iso Z X Y,
      (exp_iterated_iso X Z Y,
        (exp_unit_iso Y, exp_terminal_iso X))).
Definition high_eq_product_hom (X Y Z : @Ob C)
  : HomSet Z (X × Y) ≅[SetCat@{h p _ _ _ _ _}]
      (HomSet Z X ×S HomSet Z Y)
  := product_hom_iso X Y Z.
Definition low_eq_product_hom (X Y Z : @Ob D)
  : HomSet Z (X × Y) ≅[SetCat@{p h _ _ _ _ _}]
      (HomSet Z X ×S HomSet Z Y)
  := product_hom_iso X Y Z.
Definition high_eq_iterated_hom (X Y Z W : @Ob C)
  : HomSet W ((Y ^ X) ^ Z) ≅[SetCat@{h p _ _ _ _ _}]
      HomSet W (Y ^ (X × Z))
  := exp_iterated_hom_iso X Z Y W.
Definition low_eq_iterated_hom (X Y Z W : @Ob D)
  : HomSet W ((Y ^ X) ^ Z) ≅[SetCat@{p h _ _ _ _ _}]
      HomSet W (Y ^ (X × Z))
  := exp_iterated_hom_iso X Z Y W.

(** Public notation survives section closure and imports. *)

Definition high_eq_internal_unit (X Y Z : @Ob C) (f : Hom Z (Y ^ X))
  : idᴱ[Y] ∘ᴱ f ≈ f
  := exp_comp_id_l f.
Definition low_eq_double_curry (A B Y Z : @Ob D)
    (f : Hom (Z × (A × B)) Y)
  : (ƛ₂ f)^♭₂ ≈ f
  := exp_curry_twice_β f.

Context (F : Fct C D) (G : Fct D C)
    `{HF : !IsCCCF F} `{HG : !IsCCCF G}.

(** CCC-preservation composition permits different hom/equality orderings
    in its intermediate category. *)

Definition mixed_levels_closed_composite
  : @IsCCCF C C (G ∘F F)
  := CompF_IsCCCF F G.

(** Bundling and composing preserve both strict hom/equality orderings. *)

Definition high_eq_bundled_closed_fct
  : CCCFct C D
  := CCCFctOfIsCCCF F HF.
Definition low_eq_bundled_closed_fct
  : CCCFct D C
  := CCCFctOfIsCCCF G HG.
Definition mixed_levels_bundled_closed_composite
  : CCCFct C C
  := CompCCCF low_eq_bundled_closed_fct high_eq_bundled_closed_fct.
Definition mixed_levels_bundled_cartesian_composite
  : @CartFct C C (Cats.Cat.Cartesian.Core.hasTerminal C)
      (Cats.Cat.Cartesian.Core.hasProduct C)
  := CompCartF (CCCFctToCartFct low_eq_bundled_closed_fct)
      (CCCFctToCartFct high_eq_bundled_closed_fct).

Universe s.
Constraint l < s.
Context (J : Cat@{s s s _ _}).

(** Limit preservation does not impose an indexing bound on the shape. *)

Definition high_eq_exp_limit (A : @Ob C)
    (K : Fct J C) (L : @Ob C) (κ : L ⇒Δ K) (H : is_limit κ)
  : is_limit (MapCone (-^ A) κ)
  := exp_preserves_limit A H.
Definition low_eq_exp_limit (A : @Ob D)
    (K : Fct J D) (L : @Ob D) (κ : L ⇒Δ K) (H : is_limit κ)
  : is_limit (MapCone (-^ A) κ)
  := exp_preserves_limit A H.
End ExponentialLevels.

(** An adjunction can relate categories whose two hom levels are reversed.
    Its natural hom isomorphism uses a larger ambient set category, with
    either ordering of carrier and equality-witness levels. *)

Section AdjunctionLevels.
Universe o h p n e l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < e.
Constraint e < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (F : Fct C D) (G : Fct D C) (A : F ⊣ G).

Definition mixed_adjunct (X : @Ob C) (Y : @Ob D)
  : HomSet (F X) Y →r HomSet X (G Y)
  := adjunct_resp A.
Definition mixed_unadjunct (X : @Ob C) (Y : @Ob D)
  : HomSet X (G Y) →r HomSet (F X) Y
  := unadjunct_resp A.
Definition mixed_adj_comp
  : (F ∘F IdF) ⊣ (IdF ∘F G)
  := CompAdj A (IdAdj C).
Definition high_eq_adj_hom
  : @NatIso _ SetCat@{n e _ _ _ _ _} (LeftHomF F) (RightHomF G)
  := adj_hom_nat_iso A.
Definition low_eq_adj_hom
  : @NatIso _ SetCat@{e n _ _ _ _ _} (LeftHomF F) (RightHomF G)
  := adj_hom_nat_iso A.
End AdjunctionLevels.

(** Large diagram shapes may raise cone and law levels, without identifying
    the target category's native hom and equality-witness levels. *)

Section LimitLevels.
Universe o h p n l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < l.
Context (J : Cat@{n h p l l}).
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context `{HC : !HasLimitsOfShape C J} `{HD : !HasLimitsOfShape D J}.

Definition high_eq_limit_fct
  := @LimF J C HC.
Definition low_eq_limit_fct
  := @LimF J D HD.
Definition high_eq_limit_adj
  := @LimAdj J C HC.
Definition low_eq_limit_adj
  := @LimAdj J D HD.
Definition high_eq_limit_converse
  := limits_iff_diagonal_right_adjoint J C.
Definition low_eq_limit_converse
  := limits_iff_diagonal_right_adjoint J D.
Definition high_eq_cone_category (K : Fct J C)
  := ConeCat K.
Definition low_eq_cone_category (K : Fct J D)
  := ConeCat K.

Context (F : Fct C D) (G : Fct D C) (A : F ⊣ G).
Context (K : Fct J D) (L : @Ob D) (κ : L ⇒Δ K) (Hκ : is_limit κ).
Definition mixed_right_adjoint_limit
  : is_limit (MapCone G κ)
  := right_adjoint_preserves_limit A Hκ.
End LimitLevels.

(** Duality and colimit adjunctions preserve independent target hom/equality
    levels, even when the diagram objects live at a higher level. *)

Section ColimitLevels.
Universe o h p n l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < l.
Context (J : Cat@{n h p l l}).
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).

Definition high_eq_colimit_adj
  : HasColimitsOfShape C J ↔
      ∃ L : Fct (FctCat J C) C, L ⊣ Δ[J,C]
  := colimits_iff_diagonal_left_adjoint J C.

Definition low_eq_colimit_adj
  : HasColimitsOfShape D J ↔
      ∃ L : Fct (FctCat J D) D, L ⊣ Δ[J,D]
  := colimits_iff_diagonal_left_adjoint J D.

Definition high_eq_limit_duality (K : Fct J C) {L}
    (κ : L ⇒Δ K)
  : is_limit κ ↔ is_colimit (ConeOp κ)
  := limit_iff_op_colimit κ.

Definition low_eq_limit_duality (K : Fct J D) {L}
    (κ : L ⇒Δ K)
  : is_limit κ ↔ is_colimit (ConeOp κ)
  := limit_iff_op_colimit κ.

Context (F : Fct C D) (G : Fct D C) (A : F ⊣ G).
Context (K : Fct J C) (L : @Ob C) (κ : K ⇒∇ L).

Definition mixed_left_adjoint_colimit (Hκ : is_colimit κ)
  : is_colimit (MapCocone F κ)
  := left_adjoint_preserves_colimit A Hκ.

End ColimitLevels.

(** Named dual structures and both shape conversions preserve independent
    hom-carrier and equality-witness levels. *)

Section NamedColimitLevels.
Universes o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).

Definition high_eq_named_colimits
    (HI : HasInitial C) (HP : HasCoproduct C) (HE : HasCoequalizer C)
    (HQ : HasPushout C)
  : HasColimitsOfShape C (EmptyShape^op) ∧
      HasColimitsOfShape C (PairShape^op) ∧
      HasColimitsOfShape C (ParallelShape^op) ∧
      HasColimitsOfShape C SpanShape
  := (@InitialColimits C HI,
      (@CoproductColimits C HP,
        (@CoequalizerColimits C HE, @PushoutColimits C HQ))).

Definition low_eq_named_colimits
    (HI : HasInitial D) (HP : HasCoproduct D) (HE : HasCoequalizer D)
    (HQ : HasPushout D)
  : HasColimitsOfShape D (EmptyShape^op) ∧
      HasColimitsOfShape D (PairShape^op) ∧
      HasColimitsOfShape D (ParallelShape^op) ∧
      HasColimitsOfShape D SpanShape
  := (@InitialColimits D HI,
      (@CoproductColimits D HP,
        (@CoequalizerColimits D HE, @PushoutColimits D HQ))).

Definition high_eq_named_colimits_recovery
    (HI : HasColimitsOfShape C (EmptyShape^op))
    (HP : HasColimitsOfShape C (PairShape^op))
    (HE : HasColimitsOfShape C (ParallelShape^op))
    (HQ : HasColimitsOfShape C SpanShape)
  : HasInitial C ∧ HasCoproduct C ∧ HasCoequalizer C ∧ HasPushout C
  := (@EmptyColimitsInitial C HI,
      (@PairColimitsCoproduct C HP,
        (@ParallelColimitsCoequalizer C HE, @SpanColimitsPushout C HQ))).

Definition low_eq_named_colimits_recovery
    (HI : HasColimitsOfShape D (EmptyShape^op))
    (HP : HasColimitsOfShape D (PairShape^op))
    (HE : HasColimitsOfShape D (ParallelShape^op))
    (HQ : HasColimitsOfShape D SpanShape)
  : HasInitial D ∧ HasCoproduct D ∧ HasCoequalizer D ∧ HasPushout D
  := (@EmptyColimitsInitial D HI,
      (@PairColimitsCoproduct D HP,
        (@ParallelColimitsCoequalizer D HE, @SpanColimitsPushout D HQ))).

(** Both finite-colimit basis conversions retain independent hom/equality
    levels, in either size ordering. *)

Definition high_eq_finite_colimit_bases
  : (HasInitial C ∧ HasPushout C)
      ↔ (HasInitial C ∧ HasCoproduct C ∧ HasCoequalizer C)
  := finite_colimit_bases C.

Definition low_eq_finite_colimit_bases
  : (HasInitial D ∧ HasPushout D)
      ↔ (HasInitial D ∧ HasCoproduct D ∧ HasCoequalizer D)
  := finite_colimit_bases D.

End NamedColimitLevels.

(** Shape changes may reverse the shape hom/equality ordering and lower its
    object level. Neither ordering of the target's native hom levels changes. *)

Section ReindexedLimitLevels.
Universe o h p n m l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < m.
Constraint m < l.
Context (I : Cat@{m p h l l}) (J : Cat@{n h p l l}).
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (Q : Fct I J) (HF : is_full Q) (HQ : is_essentially_surjective Q).
Context (K : Fct J C) (K' : Fct J D).
Context (X : @Ob C) (X' : @Ob D).
Context (κ : X ⇒Δ (K ∘F Q)) (κ' : X' ⇒Δ (K' ∘F Q)).

Definition high_eq_extend_cone
  : X ⇒Δ K
  := ExtendCone HF HQ κ.
Definition low_eq_extend_cone
  : X' ⇒Δ K'
  := ExtendCone HF HQ κ'.
Definition high_eq_restrict_limit
  := limit_iff_restrict HF HQ (ExtendCone HF HQ κ).
Definition low_eq_restrict_limit
  := limit_iff_restrict HF HQ (ExtendCone HF HQ κ').

Context `{HC : !HasLimitsOfShape C I} `{HD : !HasLimitsOfShape D I}.
Definition high_eq_reindexed_limits
  : HasLimitsOfShape C J
  := ReindexedLimits HF HQ.
Definition low_eq_reindexed_limits
  : HasLimitsOfShape D J
  := ReindexedLimits HF HQ.
Definition high_eq_reindexed_limit
  : HasLimit C K
  := ReindexedLimit HF HQ K.
Definition low_eq_reindexed_limit
  : HasLimit D K'
  := ReindexedLimit HF HQ K'.

(** Cone comparisons share ambient bounds without identifying either shape's
    native levels; the ambient carrier/equality ordering can also vary. *)

Universes a b.
Constraint l < a.
Constraint a < b.

Definition high_eq_cone_comparison
  : @NatIso (C^op) SetCat@{a b _ _ _ _ _}
      (ConeF K) (ConeF (K ∘F Q))
  := cone_reindex_nat_iso HF HQ K.

Definition low_eq_cone_comparison
  : @NatIso (D^op) SetCat@{b a _ _ _ _ _}
      (ConeF K') (ConeF (K' ∘F Q))
  := cone_reindex_nat_iso HF HQ K'.

Definition high_eq_restricted_limit (HL : HasLimit C K)
  : HasLimit C (K ∘F Q)
  := @RestrictedLimit I J C Q HF HQ K HL.

Definition low_eq_restricted_limit (HL : HasLimit D K')
  : HasLimit D (K' ∘F Q)
  := @RestrictedLimit I J D Q HF HQ K' HL.
(** Both directions of colimit shape transfer retain the target's independent
    hom/equality levels. *)

Definition high_eq_colimit_shape_transfer
    (HC : HasColimit C K) (HR : HasColimit C (K ∘F Q))
  : HasColimit C K ∧ HasColimit C (K ∘F Q)
  := (@ReindexedColimit I J C Q HF HQ K HR,
      @RestrictedColimit I J C Q HF HQ K HC).

Definition low_eq_colimit_shape_transfer
    (HC : HasColimit D K') (HR : HasColimit D (K' ∘F Q))
  : HasColimit D K' ∧ HasColimit D (K' ∘F Q)
  := (@ReindexedColimit I J D Q HF HQ K' HR,
      @RestrictedColimit I J D Q HF HQ K' HC).

End ReindexedLimitLevels.

(** Finite covers do not identify the shape's object, hom or equality levels
    with those of the target category, in either hom/equality ordering. *)

Section FiniteShapeLevels.
Universe o h p n m l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < m.
Constraint m < l.
Context (J : Cat@{n p h l l}) (K : Cat@{m h p l l}).
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context `{HJ : !HasFiniteHomCover J} `{HK : !HasFiniteHomCover K}.
Context `{HGC : !HasFiniteGen J} `{HGD : !HasFiniteGen K}.
Context `{HTC : !HasTerminal C} `{HTD : !HasTerminal D}.
Context `{HPC : !HasProduct C} `{HPD : !HasProduct D}.
Context `{HEC : !HasEqualizer C} `{HED : !HasEqualizer D}.
Context `{HPbC : !HasPullback C} `{HPbD : !HasPullback D}.

Definition high_eq_finite_hom_generators
  : HasFiniteGen J
  := FiniteHomGen.
Definition low_eq_finite_hom_generators
  : HasFiniteGen K
  := FiniteHomGen.
Definition high_eq_generated_limits
  : HasLimitsOfShape C J
  := GeneratedLimits.
Definition low_eq_generated_limits
  : HasLimitsOfShape D K
  := GeneratedLimits.
Definition high_eq_finite_limits
  : HasLimitsOfShape C J
  := FiniteLimits.
Definition low_eq_finite_limits
  : HasLimitsOfShape D K
  := FiniteLimits.
Definition high_eq_finite_limit (F : Fct J C)
  : HasLimit C F
  := FiniteLimit F.
Definition low_eq_finite_limit (F : Fct K D)
  : HasLimit D F
  := FiniteLimit F.
Definition high_eq_pullback_finite_limits
  : HasLimitsOfShape C J
  := PullbackFiniteLimits.
Definition low_eq_pullback_finite_limits
  : HasLimitsOfShape D K
  := PullbackFiniteLimits.
(** Opposite finite witnesses and both bases supply colimits without
    identifying shape or target universes. *)

Context `{HIC : !HasInitial C} `{HID : !HasInitial D}.
Context `{HCC : !HasCoproduct C} `{HCD : !HasCoproduct D}.
Context `{HQC : !HasCoequalizer C} `{HQD : !HasCoequalizer D}.
Context `{HPCo : !HasPushout C} `{HPDo : !HasPushout D}.

Definition high_eq_constructed_finite_colimits
  : HasColimitsOfShape C J ∧ HasColimitsOfShape C J ∧
      HasColimitsOfShape C J ∧ HasColimitsOfShape C J
  := (GeneratedColimits,
      (FiniteColimits, (PushoutFiniteColimits, PushoutGeneratedColimits))).

Definition low_eq_constructed_finite_colimits
  : HasColimitsOfShape D K ∧ HasColimitsOfShape D K ∧
      HasColimitsOfShape D K ∧ HasColimitsOfShape D K
  := (GeneratedColimits,
      (FiniteColimits, (PushoutFiniteColimits, PushoutGeneratedColimits))).

End FiniteShapeLevels.

(** Graph edges retain independent carrier and equality levels. Paths must
    contain intermediate vertices; their generated equality also contains
    the original edge witnesses. Raising carriers does not force witnesses up. *)

Section GraphLevels.
Universe o e p n l.
Constraint o < e.
Constraint e < p.
Constraint p < n.
Constraint n < l.
Context (G : Graph@{o e p}) (H : Graph@{o p e}) (K : Graph@{n e p}).

Definition high_eq_graph_path (x y : @Vtx G)
  : Type@{e}
  := Path G x y.
Definition low_eq_graph_path (x y : @Vtx H)
  : Type@{p}
  := Path H x y.
Definition high_eq_free
  : Cat@{o e p l l}
  := FreeCat G.
Definition raised_carrier_free
  : Cat@{o n p l l}
  := FreeCat G.
Definition large_vertex_free
  : Cat@{n n n l l}
  := FreeCat K.

Context (C : Cat@{o e p l l}) (D : Cat@{o p e l l}).
Context (R : G →G UnderlyingGraph C) (S : G →G UnderlyingGraph D).
Definition high_eq_free_interpretation
  : Fct (FreeCat G) C
  := FreeF R.
Definition low_eq_free_interpretation
  : Fct (FreeCat G) D
  := FreeF S.

Definition high_eq_finite_graph {n : nat} (k : Fin n → Fin n → nat)
  : Graph@{o e p}
  := FiniteGraph k.
Definition low_eq_finite_graph {n : nat} (k : Fin n → Fin n → nat)
  : Graph@{o p e}
  := FiniteGraph k.

Context `{HEC : !HasEqualizer C} `{HED : !HasEqualizer D}.
Context `{HOC : !HasLimitsOfShape C (DiscreteCat (@Vtx G))}.
Context `{HGC : !HasLimitsOfShape C (DiscreteCat (GraphEdges G))}.
Context `{HOD : !HasLimitsOfShape D (DiscreteCat (@Vtx G))}.
Context `{HGD : !HasLimitsOfShape D (DiscreteCat (GraphEdges G))}.
Definition high_eq_graph_generated_limits
  := @GraphProductsEqualizerLimits G C HOC HGC HEC.
Definition low_eq_graph_generated_limits
  := @GraphProductsEqualizerLimits G D HOD HGD HED.

Context (HFC : ∀ x : @Vtx G,
  HasLimitsOfShape C (DiscreteCat (∃ y : @Vtx G, Edge x y))).
Context (HFD : ∀ x : @Vtx G,
  HasLimitsOfShape D (DiscreteCat (∃ y : @Vtx G, Edge x y))).
Definition high_eq_sigma_edge_products
  := @SigmaProductLimits C (@Vtx G) (λ x, ∃ y : @Vtx G, Edge x y) HOC HFC.
Definition low_eq_sigma_edge_products
  := @SigmaProductLimits D (@Vtx G) (λ x, ∃ y : @Vtx G, Edge x y) HOD HFD.
(** Opposite graph colimits need only vertex and generator-source coproducts,
    while preserving either ordering of target hom and equality levels. *)

Context `{HQC : !HasCoequalizer C} `{HQD : !HasCoequalizer D}.
Context `{HCO : !HasColimitsOfShape C (DiscreteCat (@Vtx G))}.
Context `{HCG : !HasColimitsOfShape C (DiscreteCat (GraphEdges (G^opG)))}.
Context `{HDO : !HasColimitsOfShape D (DiscreteCat (@Vtx G))}.
Context `{HDG : !HasColimitsOfShape D (DiscreteCat (GraphEdges (G^opG)))}.

Definition high_eq_graph_colimits
  : HasColimitsOfShape C (FreeCat G)
  := GraphCoproductsCoequalizerColimits.

Definition low_eq_graph_colimits
  : HasColimitsOfShape D (FreeCat G)
  := GraphCoproductsCoequalizerColimits.

End GraphLevels.


(** Shape comparisons and their diagonal adjunctions must work in either
    ordering of the target category's native hom and equality levels. *)

Section ShapedLimitLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context `{HC : !HasProduct C} `{HD : !HasProduct D}.
Context `{HPC : !HasPullback C} `{HPD : !HasPullback D}.
Context `{HTC : !HasTerminal C} `{HTD : !HasTerminal D}.
Context `{HEC : !HasEqualizer C} `{HED : !HasEqualizer D}.

Definition high_eq_product_diagonal
  := @LimAdj PairShape C (ProductLimits (C := C)).
Definition low_eq_product_diagonal
  := @LimAdj PairShape D (ProductLimits (C := D)).
Definition high_eq_pullback_diagonal
  := @LimAdj CospanShape C (PullbackLimits (C := C)).
Definition low_eq_pullback_diagonal
  := @LimAdj CospanShape D (PullbackLimits (C := D)).
Definition high_eq_empty_diagonal
  := @LimAdj EmptyShape C (TerminalLimits (C := C)).
Definition low_eq_empty_diagonal
  := @LimAdj EmptyShape D (TerminalLimits (C := D)).
Definition high_eq_equalizer_diagonal
  := @LimAdj ParallelShape C (EqualizerLimits (C := C)).
Definition low_eq_equalizer_diagonal
  := @LimAdj ParallelShape D (EqualizerLimits (C := D)).
Definition high_eq_terminal_from_limits
  := @EmptyLimitsTerminal C (TerminalLimits (C := C)).
Definition low_eq_terminal_from_limits
  := @EmptyLimitsTerminal D (TerminalLimits (C := D)).
Definition high_eq_equalizer_from_limits
  := @ParallelLimitsEqualizer C (EqualizerLimits (C := C)).
Definition low_eq_equalizer_from_limits
  := @ParallelLimitsEqualizer D (EqualizerLimits (C := D)).
Definition high_eq_products_from_pullbacks
  : HasProduct C
  := @PullbackProduct C HTC HPC.
Definition low_eq_products_from_pullbacks
  : HasProduct D
  := @PullbackProduct D HTD HPD.
Definition high_eq_equalizers_from_pullbacks
  : HasEqualizer C
  := @PullbackEqualizer C HTC HPC.
Definition low_eq_equalizers_from_pullbacks
  : HasEqualizer D
  := @PullbackEqualizer D HTD HPD.
Definition high_eq_pullbacks_from_equalizers
  : HasPullback C
  := @ProductEqualizerPullback C HC HEC.
Definition low_eq_pullbacks_from_equalizers
  : HasPullback D
  := @ProductEqualizerPullback D HD HED.
Definition high_eq_finite_limit_bases
  := finite_limit_bases C.
Definition low_eq_finite_limit_bases
  := finite_limit_bases D.
Definition high_eq_finite_products (n : nat)
  := @FiniteProductLimits C HTC HC n.
Definition low_eq_finite_products (n : nat)
  := @FiniteProductLimits D HTD HD n.
Definition high_eq_finite_graph_limits {n : nat} (k : Fin n → Fin n → nat)
  := @FiniteGraphLimits C HTC HC HEC n k.
Definition low_eq_finite_graph_limits {n : nat} (k : Fin n → Fin n → nat)
  := @FiniteGraphLimits D HTD HD HED n k.
End ShapedLimitLevels.

(** The two product indices can be larger than the target homs. The general
    equalizer formula must preserve both native hom/equality orderings. *)

Section ProductEqualizerConstructionLevels.
Universe o h p n l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < l.
Context (J : Cat@{n h p l l}).
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context `{HEC : !HasEqualizer C} `{HED : !HasEqualizer D}.
Context `{HOC : !HasLimitsOfShape C (DiscreteCat (@Ob J))}.
Context `{HAC : !HasLimitsOfShape C (DiscreteCat (ArrowOb J))}.
Context `{HOD : !HasLimitsOfShape D (DiscreteCat (@Ob J))}.
Context `{HAD : !HasLimitsOfShape D (DiscreteCat (ArrowOb J))}.

Definition high_eq_product_equalizer_limits
  := @IndexedProductsEqualizerLimits J C HOC HAC HEC.
Definition low_eq_product_equalizer_limits
  := @IndexedProductsEqualizerLimits J D HOD HAD HED.
Definition high_eq_product_equalizer_limit (K : Fct J C)
  := ProductsEqualizerLimit K.
Definition low_eq_product_equalizer_limit (K : Fct J D)
  := ProductsEqualizerLimit K.
(** The dual constructor needs only its two discrete coproduct choices;
    these large indices do not constrain the target hom/equality order. *)

Context `{HQC : !HasCoequalizer C} `{HQD : !HasCoequalizer D}.
Context `{HCO : !HasColimitsOfShape C (DiscreteCat (@Ob J))}.
Context `{HCA : !HasColimitsOfShape C (DiscreteCat (ArrowOb (J^op)))}.
Context `{HDO : !HasColimitsOfShape D (DiscreteCat (@Ob J))}.
Context `{HDA : !HasColimitsOfShape D (DiscreteCat (ArrowOb (J^op)))}.

Definition high_eq_coproduct_coequalizer_colimits
  : HasColimitsOfShape C J
  := IndexedCoproductsCoequalizerColimits.

Definition low_eq_coproduct_coequalizer_colimits
  : HasColimitsOfShape D J
  := IndexedCoproductsCoequalizerColimits.

End ProductEqualizerConstructionLevels.

(** Small index categories do not identify the target category's native
    hom and equality-witness levels, including diagrams with relations. *)

Section SmallShapeLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (X Y Z W : @Ob C) (X' Y' Z' W' : @Ob D).
Context (f : Hom X Y) (g : Hom X Z) (r : Hom Y W) (s : Hom Z W).
Context (f' : Hom X' Y') (g' : Hom X' Z') (r' : Hom Y' W') (s' : Hom Z' W').
Context (H : r ∘ f ≈ s ∘ g) (H' : r' ∘ f' ≈ s' ∘ g').

Definition high_eq_arrow_shape
  := ArrowDiagram f.
Definition low_eq_arrow_shape
  := ArrowDiagram f'.
Definition high_eq_span_shape
  := SpanDiagram f g.
Definition low_eq_span_shape
  := SpanDiagram f' g'.
Definition high_eq_parallel_shape
  := ParallelDiagram (r ∘ f) (s ∘ g).
Definition low_eq_parallel_shape
  := ParallelDiagram (r' ∘ f') (s' ∘ g').
Definition high_eq_square_shape
  := SquareDiagram f g r s H.
Definition low_eq_square_shape
  := SquareDiagram f' g' r' s' H'.
Definition high_eq_iso_shape (i : X ≅[C] Y)
  := IsoDiagram i.
Definition low_eq_iso_shape (i : X' ≅[D] Y')
  := IsoDiagram i.

Context (V : Type@{o}) (R : V → V → Type@{h}) `{HR : !PreOrder R}.
Definition small_eq_preorder
  : Cat@{o h Set l l}
  := PreorderCat R.
End SmallShapeLevels.

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

Definition independent_hom (X Y : ObB K)
  : Cat@{h t p l l}
  := HomCat X Y.
Definition independent_hom_reverse (X Y : ObB L)
  : Cat@{h p t l l}
  := HomCat X Y.
Definition independent_cells (X Y : ObB K)
  : Type@{h}
  := Cell1 X Y.
End BicategoryLevels.

(** Representability and the Yoneda isomorphism retain both hom/equality
    orderings; the isomorphism uses a large enough ambient set category. *)

Section RepresentableLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (F : Fct C SetCat@{h p _ _ _ _ _}).
Context (P : Fct (D^op) SetCat@{p h _ _ _ _ _}).

Definition high_eq_universal_elements
  := @represents_iff_universal_element C F.
Definition low_eq_universal_elements
  := @represents_op_iff_universal_element D P.
Definition high_eq_representing_objects
  := @representation_iso C F.
Definition low_eq_representing_objects
  := @representation_op_iso D P.
Definition high_eq_yoneda
  := @yoneda_lemma_iso C F.
Definition low_eq_yoneda
  := @yoneda_lemma_iso (D^op) P.
End RepresentableLevels.

(** The chosen pullback instance formerly collapsed these two levels. *)

Section SetoidPullbackLevels.
Universe u p.
Constraint p < u.
Context (X Y : SetC@{u p}) (f : X →r Y).
Definition distinct_setoid_pullbacks
  : HasPullback (SetCat@{u p _ _ _ _ _})
  := SetCat_HasPullback.
Definition distinct_sum_reindex
  := fam_sum_reindex_nat_iso f.
Definition distinct_fam_slice_equivalence
  := fam_slice_equiv X.
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

Definition high_eq_code_model
  : CwF (SetCat@{u p _ _ _ _ _})
  := SetCwF El.
Definition low_eq_code_model
  : CwF (SetCat@{p u _ _ _ _ _})
  := SetCwF El'.
Definition reverse_code_model
  : CwF (SetCat@{u p _ _ _ _ _})
  := SetCwF El''.
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
Context (T : Fct (C^op) FamCat) (U : Fct (D^op) FamCat).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).

Definition high_eq_rep_types (Γ : @Ob C)
  : SetC@{a c}
  := Ty T Γ.
Definition high_eq_rep_terms (Γ : @Ob C) (A : Ty T Γ)
  : SetC@{b d}
  := Tm T Γ A.
Definition low_eq_rep_types (Γ : @Ob D)
  : SetC@{c a}
  := Ty U Γ.
Definition low_eq_rep_terms (Γ : @Ob D) (A : Ty U Γ)
  : SetC@{d b}
  := Tm U Γ A.
Definition high_eq_context_pairs (Γ Δ : @Ob C) (A : Ty T Γ)
  : SetC@{b d}
  := ContextPairS T A Δ.
Definition low_eq_context_pairs (Γ Δ : @Ob D) (A : Ty U Γ)
  : SetC@{d b}
  := ContextPairS U A Δ.
Definition high_eq_representation
  := @context_extension_nat_iso C T HC.
Definition low_eq_representation
  := @context_extension_nat_iso D U HU.
Definition high_eq_context_conversion
  := @context_conv_iso C T HC.
Definition low_eq_context_conversion
  := @context_conv_iso D U HU.
Definition high_eq_display_pullback
  := @context_lift_pullback C T HC.
Definition low_eq_display_pullback
  := @context_lift_pullback D U HU.
Definition high_eq_coherent_display
  : HasDisplay C (FamBaseF ∘F T)
  := @ContextExtension_HasDisplay C T HC.
Definition low_eq_coherent_display
  : HasDisplay D (FamBaseF ∘F U)
  := @ContextExtension_HasDisplay D U HU.
Definition high_eq_display_conversion
  := @display_conv_iso C (FamBaseF ∘F T)
  high_eq_coherent_display.
Definition low_eq_display_conversion
  := @display_conv_iso D (FamBaseF ∘F U)
  low_eq_coherent_display.
Definition high_eq_display_presheaf
  := @DisplayTyTmF C (FamBaseF ∘F T)
  high_eq_coherent_display.
Definition low_eq_display_presheaf
  := @DisplayTyTmF D (FamBaseF ∘F U)
  low_eq_coherent_display.
Definition high_eq_display_terms (Γ : @Ob C) (A : Ty T Γ)
  : SetC@{p p}
  := Tm high_eq_display_presheaf Γ A.
Definition low_eq_display_terms (Γ : @Ob D) (A : Ty U Γ)
  : SetC@{p h}
  := Tm low_eq_display_presheaf Γ A.
Definition high_eq_context_maps (X Y : ContextType T)
  : SetC@{p p}
  := @HomSet (ContextTypeCat T) X Y.
Definition low_eq_context_maps (X Y : ContextType U)
  : SetC@{p h}
  := @HomSet (ContextTypeCat U) X Y.
Definition high_eq_cwf_comprehension
  := @CwFComprehension C T HC.
Definition low_eq_cwf_comprehension
  := @CwFComprehension D U HU.
Definition high_eq_full_comprehension
  := @cwf_comprehension_fully_faithful C T HC.
Definition low_eq_full_comprehension
  := @cwf_comprehension_fully_faithful D U HU.
Definition high_eq_term_sections
  := @context_term_section_iso C T HC.
Definition low_eq_term_sections
  := @context_term_section_iso D U HU.
Definition high_eq_context_representations
  := @context_extension_iff_representation C T.
Definition low_eq_context_representations
  := @context_extension_iff_representation D U.
Definition high_eq_represented_cwf
  := @RepresentedCwF C T.
Definition low_eq_represented_cwf
  := @RepresentedCwF D U.
End ContextRepresentationLevels.

(** Universal pairs recover extensions even when section carriers contain
    larger hom-equality witnesses. Fix small type presheaves and independent
    hom/equality levels, with a still larger category-law bound. *)

Section ContextUniversalLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (P : Fct (C^op) SetCat@{Set Set _ _ _ _ _})
    (Q : Fct (D^op) SetCat@{Set Set _ _ _ _ _}).
Context (HD : HasDisplay C P) (HE : HasDisplay D Q).

Let T
  : Fct (C^op) FamCat@{_ _ _ _ _ Set Set p p p _ _ _ _ _ _}
  := @DisplayTyTmF C P HD.
Let U
  : Fct (D^op) FamCat@{_ _ _ _ _ Set Set p p h _ _ _ _ _ _}
  := @DisplayTyTmF D Q HE.

Definition high_eq_universal_terms (Γ : @Ob C) (A : Ty T Γ)
  : SetC@{p p}
  := Tm T Γ A.
Definition low_eq_universal_terms (Γ : @Ob D) (A : Ty U Γ)
  : SetC@{p h}
  := Tm U Γ A.
Definition high_eq_universal_criterion
  := @context_extension_iff_universal_element C T.
Definition low_eq_universal_criterion
  := @context_extension_iff_universal_element D U.
Definition high_eq_universal_representation
  := @context_extension_lifted_representation C T.
Definition low_eq_universal_representation
  := @context_extension_lifted_representation D U.
Definition high_eq_universal_mediator
  := @context_extension_universal_mediator C T.
Definition low_eq_universal_mediator
  := @context_extension_universal_mediator D U.
Definition high_eq_display_universal {Γ : @Ob C} (A : P Γ)
  : (@display_generic_pair C P HD Γ A) ⦂ Univ(ContextPairF T A)
  := @display_pair_universal C P HD Γ A.
Definition low_eq_display_universal {Γ : @Ob D} (A : Q Γ)
  : (@display_generic_pair D Q HE Γ A) ⦂ Univ(ContextPairF U A)
  := @display_pair_universal D Q HE Γ A.
Definition high_eq_display_lifted {Γ : @Ob C} (A : P Γ)
  : Display P A ⦂ Rep↑ ContextPairF T A
  := @display_representation C P HD Γ A.
Definition low_eq_display_lifted {Γ : @Ob D} (A : Q Γ)
  : Display Q A ⦂ Rep↑ ContextPairF U A
  := @display_representation D Q HE Γ A.
Definition high_eq_display_recovery
  : HasContextExtension T
  := @Display_HasContextExtension C P HD.
Definition low_eq_display_recovery
  : HasContextExtension U
  := @Display_HasContextExtension D Q HE.
Definition high_eq_display_model_terms (HT : HasTerminal C)
    (Γ : @Ob C) (A : P Γ)
  : SetC@{p p}
  := Tm (@DisplayCwF C P HD HT) Γ A.
Definition low_eq_display_model_terms (HT : HasTerminal D)
    (Γ : @Ob D) (A : Q Γ)
  : SetC@{p h}
  := Tm (@DisplayCwF D Q HE HT) Γ A.
End ContextUniversalLevels.

(** Comprehension over type elements keeps large type carriers/equalities
    independent of base homs and of the recovered term bounds. Both orders
    also check the total-space natural isomorphism. *)

Section ComprehensionElementLevels.
Universe o h p l a b.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint l < a.
Constraint a < b.
Constraint b < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (P : Fct (C^op) SetCat@{a b _ _ _ _ _})
    (Q : Fct (D^op) SetCat@{b a _ _ _ _ _}).
Definition high_eq_elements
  : Cat@{o b p _ _}
  := ElementsCat P.
Definition low_eq_elements
  : Cat@{o a h _ _}
  := ElementsCat Q.
Definition high_eq_elements_lifts
  : HasCartLift (ElementsBaseF P)
  := ElementsBaseF_HasCartesianLift P.
Definition low_eq_elements_lifts
  : HasCartLift (ElementsBaseF Q)
  := ElementsBaseF_HasCartesianLift Q.
Context (K : Comprehension (ElementsBaseF P))
    (L : Comprehension (ElementsBaseF Q)).
Definition high_eq_comprehension_display
  : HasDisplay C P
  := Comprehension_HasDisplay P K.
Definition low_eq_comprehension_display
  : HasDisplay D Q
  := Comprehension_HasDisplay Q L.
Definition high_eq_comprehension_terms (HT : HasTerminal C)
    (Γ : @Ob C) (A : P Γ)
  : SetC@{p p}
  := Tm (@ComprehensionCwF C P K HT) Γ A.
Definition low_eq_comprehension_terms (HT : HasTerminal D)
    (Γ : @Ob D) (A : Q Γ)
  : SetC@{p h}
  := Tm (@ComprehensionCwF D Q L HT) Γ A.
Definition high_eq_elements_criterion
  : HasDisplay C P ↔ Comprehension (ElementsBaseF P)
  := display_iff_elements_comprehension P.
Definition low_eq_elements_criterion
  : HasDisplay D Q ↔ Comprehension (ElementsBaseF Q)
  := display_iff_elements_comprehension Q.
Definition high_eq_comprehension_iso
  : @DisplayElementsF C P (Comprehension_HasDisplay P K) ≅N ExtF K
  := comprehension_display_iso P K.
Definition low_eq_comprehension_iso
  : @DisplayElementsF D Q (Comprehension_HasDisplay Q L) ≅N ExtF L
  := comprehension_display_iso Q L.
End ComprehensionElementLevels.

(** Raw syntax accepts arbitrary signature levels. An inferred extra universe
    on variable markers must not restrict rename/substitution clients. *)

Section STLCSyntaxLevels.
Universe b.
Context (B : Type@{b}) (Γ Δ : Ctx B) (A : STLC.Syntax.Ty B).
Context (t : STLC.Syntax.Tm Γ A) (ρ : Ren Δ Γ)
    (σ : STLC.Substitution.Sub Δ Γ).

Definition universe_polymorphic_rename
  : STLC.Syntax.Tm Δ A
  := rename t ρ.
Definition universe_polymorphic_substitution
  : STLC.Syntax.Tm Δ A
  := subst t σ.
End STLCSyntaxLevels.

(** Beta/eta witnesses can live strictly above the raw syntax. These interfaces
    must preserve that level when packaging sets and respectful operations. *)

Section STLCEqualityLevels.
Universe b e.
Constraint b < e.
Context (B : Type@{b}) (Γ Δ : Ctx B) (A : STLC.Syntax.Ty B).
Context (t : STLC.Syntax.Tm Γ A) (ρ : Ren Δ Γ)
    (σ : STLC.Substitution.Sub Δ Γ).

Definition high_eq_syntactic_terms
  : SetC@{b e}
  := TmS Γ A.
Definition high_eq_syntactic_substitutions
  : SetC@{b e}
  := SubS Δ Γ.
Definition high_eq_syntactic_renaming
  : TmS@{b e} Γ A →r TmS@{b e} Δ A
  := tm_rename_resp ρ.
Definition high_eq_syntactic_substitution
  : TmS@{b e} Γ A →r TmS@{b e} Δ A
  := tm_subst_resp σ.
Definition high_eq_syntactic_assignment
  : SubS@{b e} Δ Γ →r TmS@{b e} Δ A
  := tm_subst_assignment_resp t.
End STLCEqualityLevels.

(** Contexts, beta/eta witnesses and category laws admit three strictly
    increasing levels. Chosen terminal/product/CCC structures and context
    packing isomorphisms preserve them. *)

Section STLCCategoryLevels.
Universe b e l.
Constraint b < e.
Constraint e < l.
Context (B : Type@{b}).

Definition separated_syntactic_category
  : Cat@{b b e l l}
  := CtxCat B.
Definition separated_syntactic_terminal
  : HasTerminal separated_syntactic_category
  := CtxCat_HasTerminal B.
Definition separated_syntactic_products
  : HasProduct separated_syntactic_category
  := CtxCat_HasProduct B.
Definition separated_syntactic_packing (Γ : Ctx B)
  : Γ ≅[separated_syntactic_category] ctx_snoc ctx_empty (CtxTy Γ)
  := ctx_pack_iso Γ.
Definition separated_syntactic_ccc
  : CCC@{b b e l l}
  := CtxCat_CCC B.
Definition separated_type_syntactic_ccc
  : CCC@{b b e l l}
  := TyCat_CCC B.

Definition separated_stlc_completeness (Γ : Ctx B) (A : STLC.Syntax.Ty B)
    (t u : STLC.Syntax.Tm Γ A)
  : TmEq@{b e _} t u ↔ TmModelEq@{b e l _ _ _} t u
  := tm_soundness_iff_completeness t u.

(** Inhabitation uses the same separated model bounds and retains a chosen
    morphism for every model, with both directions living in [Type]. *)

Definition separated_stlc_inhabitation (Γ : Ctx B) (A : STLC.Syntax.Ty B)
  : STLC.Syntax.Tm Γ A ↔
      ∀ (C : CCC@{b b e l l}) (I : B → @Ob C),
      (@Hom C) (@CtxI B C I Γ) (@TyI B C I A)
  := tm_inhabitation_soundness_iff_completeness Γ A.

Definition separated_stlc_presentations
  : (TyCat@{b e l} B) ≅[CatCat] (CtxCat@{b e l} B)
  := ContextCategoryEquivalence B.
End STLCCategoryLevels.

(** Semantic interpretation preserves separated syntax levels and permits
    either ordering of target hom carriers and equality witnesses. *)

Section STLCInterpretationLevels.
Universes b e l o h p a.
Constraint b < e.
Constraint e < l.
Constraint h < p.
Constraint p < a.
Context (B : Type@{b}) (C : CCC@{o h p a a})
    (D : CCC@{o p h a a}).
Context (I : B → @Ob C) (J : B → @Ob D).

Definition high_eq_stlc_interpretation
  : Fct (CtxCat@{b e l} B) C
  := InterpretF I.
Definition low_eq_stlc_interpretation
  : Fct (CtxCat@{b e l} B) D
  := InterpretF J.

(** Existing interpretation preservation packages without changing its
    syntax levels or requiring migration of the fixed-functor clients. *)

Definition high_eq_bundled_type_interpretation
  : CCCFct (TyCat_CCC B) C
  := CCCFctOfIsCCCF (C := TyCat_CCC B) (TypeInterpretF I) (TypeInterpretF_IsCCCF I).
Definition low_eq_bundled_type_interpretation
  : CCCFct (TyCat_CCC B) D
  := CCCFctOfIsCCCF (C := TyCat_CCC B) (TypeInterpretF J) (TypeInterpretF_IsCCCF J).

Context (F : Fct (TyCat@{b e l} B) C)
    (HF : @IsCCCF (TyCat_CCC B) C F).
Local Existing Instance HF.
Context (β : ∀ b, I b ≅[C] F (ty_base b)).

Definition separated_stlc_model_comparison
  : TypeInterpretF I ≅N F
  := type_interpretation_nat_iso F I β.

Definition separated_stlc_free_extension
  : ∃ α : TypeInterpretF I ≅N F,
      is_unique (λ η : TypeInterpretF I ⇒ F,
        ∀ b, η (ty_base b) ≈ (β b).1) α.1
  := type_interpretation_universal F I β.
End STLCInterpretationLevels.

(** Groupoid inverses, opposition, products and functor categories preserve
    either ordering of hom carriers and equality witnesses. *)

Section GroupoidLevels.
Universes o h p l.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l})
    (HC : IsGpd C) (HD : IsGpd D).
Local Existing Instance HC.
Local Existing Instance HD.

Definition high_eq_groupoid_inverse {X Y : @Ob C} (f : Hom X Y)
  : Hom Y X
  := f⁻¹.

Definition low_eq_groupoid_inverse_fct
  : Fct (D^op) D
  := InvF D.

Definition high_eq_opposite_groupoid
  : (C^op) ⦂ Gpd
  := op_IsGpd C.

Definition mixed_groupoid_product
  : (C ×C D) ⦂ Gpd
  := ProdCat_IsGpd C D.

Definition low_eq_fct_groupoid
  : (FctCat C D) ⦂ Gpd
  := FctCat_IsGpd C D.
End GroupoidLevels.

(** Setoid elements and their equality witnesses remain independent in the
    equality groupoid; its equality between parallel arrows is small. *)

Section EqualityGroupoidLevels.
Universes u p l.
Constraint u < p.
Constraint p < l.
Context (X : SetC@{u p}) (Y : SetC@{p u}).

Definition high_witness_equality_groupoid
  : Cat@{u p Set l l}
  := EqGpd X.

Definition low_witness_equality_groupoid
  : Cat@{p u Set l l}
  := EqGpd Y.

Definition separated_equality_groupoid_structure
  : high_witness_equality_groupoid ⦂ Gpd
  := EqGpd_IsGpd X.
End EqualityGroupoidLevels.

(** Delooping and the regular action preserve independent carrier and
    equality-witness sizes, in both orders. Law bounds are auxiliary. *)

Section GroupDeloopingLevels.
Universes u p l.
Constraint u < p.
Constraint p < l.
Context (X : Group@{u p l}) (Y : Group@{p u l}).

Definition high_eq_group_category
  : Cat@{Set u p l l}
  := B(X).

Definition low_eq_group_category
  : Cat@{Set p u l l}
  := B(Y).

Definition high_eq_group_category_structure
  : high_eq_group_category ⦂ Gpd
  := MonoidCat_IsGpd X.

Definition low_eq_group_category_structure
  : low_eq_group_category ⦂ Gpd
  := MonoidCat_IsGpd Y.

Definition high_eq_regular_action
  : Fct high_eq_group_category SetCat@{u p _ _ _ _ _}
  := RegularActionF X.

Definition low_eq_regular_action
  : Fct low_eq_group_category SetCat@{p u _ _ _ _ _}
  := RegularActionF Y.

Definition high_eq_endomorphism_group
  : Group@{u p l}
  := EndGroup (HC := high_eq_group_category_structure)
      high_eq_group_category tt.

Definition low_eq_endomorphism_group
  : Group@{p u l}
  := EndGroup (HC := low_eq_group_category_structure)
      low_eq_group_category tt.

Example high_eq_endomorphism_carrier
  : (high_eq_endomorphism_group : SetC@{u p}) = (X : SetC@{u p}).
Proof. reflexivity. Qed.

Example low_eq_endomorphism_carrier
  : (low_eq_endomorphism_group : SetC@{p u}) = (Y : SetC@{p u}).
Proof. reflexivity. Qed.
End GroupDeloopingLevels.

(** Family-action equivalence allows base carrier and equality levels above
    both fiber levels, in either ordering. Auxiliary law bounds remain large. *)

Section FamilyActionLevels.
Universes u p b e l.
Constraint u < p.
Constraint p < b.
Constraint b < e.
Constraint e < l.
Context (X : SetC@{b e}) (Y : SetC@{e b}).

Definition high_eq_family_action_equivalence
  : FamSCat X ≃C FctCat (EqGpd X) SetCat@{u p _ l _ _ _}
  := fam_action_equiv X.

Definition low_eq_family_action_equivalence
  : FamSCat X ≃C FctCat (EqGpd X) SetCat@{p u _ l _ _ _}
  := fam_action_equiv X.

Definition reversed_base_family_action_equivalence
  : FamSCat Y ≃C FctCat (EqGpd Y) SetCat@{u p _ l _ _ _}
  := fam_action_equiv Y.

Definition reversed_base_low_eq_family_action_equivalence
  : FamSCat Y ≃C FctCat (EqGpd Y) SetCat@{p u _ l _ _ _}
  := fam_action_equiv Y.
End FamilyActionLevels.

(** The action-slice specialization retains the family-slice size bound,
    while admitting a strictly smaller base-equality universe. *)

Section ActionSliceLevels.
Universes u p.
Constraint p < u.
Context (X : SetC@{u p}).

Definition distinct_action_slice_equivalence
  : FctCat (EqGpd X) SetCat@{u p _ _ _ _ _} ≃C
      (SetCat@{u p _ _ _ _ _} /C X)
  := action_slice_equiv X.
End ActionSliceLevels.

(** Interpreting finite ordinals in the category of categories does not raise
    the simplex category's object, arrow, equality or law universes. *)

Definition small_simplex_category
  : Cat@{Set Set Set Set Set}
  := SimplexCat.

(** Standard simplices and their Yoneda correspondence admit either ordering
    of the carrier and equality levels of the simplicial set's values. *)

Section SimplicialLevels.
Universes u p.
Constraint u < p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (Y : Fct (Δ^op) SetCat@{p u _ _ _ _ _}).

Definition high_eq_standard_simplex (n : nat)
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Δ[n].

Definition low_eq_standard_simplex (n : nat)
  : Fct (Δ^op) SetCat@{p u _ _ _ _ _}
  := Δ[n].

Definition high_eq_simplex_yoneda (n : nat)
  : LiftS (Nat_SetS Δ[n] X) ≅[SetCat] LiftS (X n)
  := simplex_element_iso n.

Definition low_eq_simplex_yoneda (n : nat)
  : LiftS (Nat_SetS Δ[n] Y) ≅[SetCat] LiftS (Y n)
  := simplex_element_iso n.

(** Standard-simplex comparisons retain both orderings after passing through
    the general category-probe construction. *)

Definition high_eq_standard_nerve (n : nat)
  : (Δ[n] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N N≅([Ord n])
  := standard_nerve_iso n.

Definition low_eq_standard_nerve (n : nat)
  : (Δ[n] : Fct (Δ^op) SetCat@{p u _ _ _ _ _}) ≅N N≅([Ord n])
  := standard_nerve_iso n.
End SimplicialLevels.

(** Small ordinal probes accept larger categories with independent object,
    arrow and equality sizes. Value equality need not dominate object size,
    and can also be raised above the value carrier. *)

Section NerveLevels.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.
Context (C : Cat@{o h e l l}) (D : Cat@{e h o l l}).

Definition low_eq_large_diagram_nerve
  : Fct (Δ^op) SetCat@{u h _ _ _ _ _}
  := N≅(C).

Definition high_eq_large_diagram_nerve
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := N≅(D).
End NerveLevels.

(** Native monoid nerves retain either ordering of carrier and equality
    levels. Their diagram comparisons raise both sides explicitly, with
    either ordering also permitted at the common ambient sizes. *)

Section MonoidNerveLevels.
Universes u p c e.
Constraint u < p.
Constraint p < c.
Constraint c < e.
Context (M : Monoid@{u p _}) (N : Monoid@{p u _}).

Definition high_eq_monoid_nerve
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Nₘ(M).

Definition low_eq_monoid_nerve
  : Fct (Δ^op) SetCat@{p u _ _ _ _ _}
  := Nₘ(N).

Definition high_eq_monoid_comparison
  : (LiftF ∘F Nₘ(M) : Fct (Δ^op) SetCat@{c e _ _ _ _ _}) ⇒ N≅(B(M))
  := MonoidDiagramN.

Definition low_eq_monoid_comparison
  : (LiftF ∘F Nₘ(N) : Fct (Δ^op) SetCat@{e c _ _ _ _ _}) ⇒ N≅(B(N))
  := MonoidDiagramN.
End MonoidNerveLevels.

(** Vertex labels and ambient homs retain independent carrier/equality sizes.
    In particular, value equality need not dominate the vertex carrier.
    Both orderings also survive the forgetful diagram comparison. *)

Section VertexNerveLevels.
Universes e h o l u p v q.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.
Constraint p < v.
Constraint v < q.
Context (X : SetC@{o e}) (Y : SetC@{e o})
    (C : Cat@{o h e l l}) (D : Cat@{e h o l l})
    (T : Fct (EqGpd X) C) (S : Fct (EqGpd Y) D).

(** Transport-preserving functors keep hom-comparison sizes independent
    of stored functor laws, even when source and target sizes are exchanged. *)

Definition forward_vertex_fct_set
  : SetC@{l o}
  := VtxFctS T S.

Definition reverse_vertex_fct_set
  : SetC@{l h}
  := VtxFctS S T.

(** The nerve map admits common value equality strictly below or above
    its value carrier, with independent native source and target homs. *)

Definition low_eq_vertex_fct_map
  : VtxFctS T S →r Nat_SetS
      (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) (Nᵥ(S))
  := vertex_nerve_resp T S.

Definition high_eq_vertex_fct_map
  : VtxFctS T S →r Nat_SetS
      (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (Nᵥ(S))
  := vertex_nerve_resp T S.

(** Reconstruction returns to the native hom-setoid even when the nerve
    equality universe lies below or above its carrier universe. *)

Definition low_eq_vertex_fct_inverse
  : Nat_SetS (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) (Nᵥ(S)) →r
      VtxFctS T S
  := vertex_nerve_inv_resp T S.

Definition high_eq_vertex_fct_inverse
  : Nat_SetS (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (Nᵥ(S)) →r
      VtxFctS T S
  := vertex_nerve_inv_resp T S.

Definition reverse_vertex_fct_inverse
  : Nat_SetS (Nᵥ(S) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) (Nᵥ(T)) →r
      VtxFctS S T
  := vertex_nerve_inv_resp S T.

(** The hom isomorphism uses ordinary common lifts, with common equality
    below or above the common carrier, without resizing native sizes. *)

Definition low_eq_vertex_hom_isomorphism
  : LiftS@{_ _ v p} (VtxFctS T S) ≅[SetCat]
      LiftS@{_ _ v p} (Nat_SetS
        (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) (Nᵥ(S)))
  := vertex_nerve_hom_iso T S.

Definition high_eq_vertex_hom_isomorphism
  : LiftS@{_ _ v q} (VtxFctS T S) ≅[SetCat]
      LiftS@{_ _ v q} (Nat_SetS
        (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (Nᵥ(S)))
  := vertex_nerve_hom_iso T S.

Definition low_eq_vertex_nerve
  : Fct (Δ^op) SetCat@{u h _ _ _ _ _}
  := Nᵥ(T).

Definition high_eq_vertex_nerve
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Nᵥ(S).

Definition low_eq_vertex_diagram_comparison
  : (Nᵥ(T) : Fct (Δ^op) SetCat@{u h _ _ _ _ _}) ⇒ N≅(C)
  := VtxDiagramN T.

Definition high_eq_vertex_diagram_comparison
  : (Nᵥ(S) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ N≅(D)
  := VtxDiagramN S.

(** Chain data need not carry the larger diagram-law universe. Equality
    remains independent of the native vertex and arrow carriers. *)

Definition low_eq_vertex_chains (n : nat)
  : SetC@{o e}
  := VtxChainS T n.

Definition high_eq_vertex_chains (n : nat)
  : SetC@{h o}
  := VtxChainS S n.

(** The spine isomorphism also admits both orderings of value sizes. *)

Definition low_eq_vertex_spine (n : nat)
  : (Nᵥ(T) : Fct (Δ^op) SetCat@{u h _ _ _ _ _}) n ≅[SetCat]
      LiftS (VtxChainS T n)
  := vertex_spine_iso T n.

Definition high_eq_vertex_spine (n : nat)
  : (Nᵥ(S) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) n ≅[SetCat]
      LiftS (VtxChainS S n)
  := vertex_spine_iso S n.

(** Arbitrary category nerves admit unique boundary filling at both strict
    universe orders, without assuming either category is a groupoid. *)

Definition low_eq_vertex_coskeletal
  : (Nᵥ(T) : Fct (Δ^op) SetCat@{u h _ _ _ _ _}) ⦂ Cosk[2%nat]
  := vertex_IsCoskeletal T.

Definition high_eq_vertex_coskeletal
  : (Nᵥ(S) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⦂ Cosk[2%nat]
  := vertex_IsCoskeletal S.

(** Local horn isomorphisms retain native hom and equality sizes. Their
    realized fillers also admit either ordering of the ambient value sizes. *)

Context `{HC : !IsGpd C} `{HD : !IsGpd D}.

Definition low_eq_outer_horn (A B E : @Ob C)
  : TriangleS C A B E ≅[SetCat] Horn2S C A B E fin_first
  := horn2_0_iso.

Definition high_eq_outer_horn (A B E : @Ob D)
  : TriangleS D A B E ≅[SetCat]
      Horn2S D A B E (fin_next (fin_next fin_first))
  := horn2_2_iso.

Definition low_eq_local_horn (A B E : X)
  : Horn2S (VtxCat T) A B E fin_first →r
      (Nᵥ(T) : Fct (Δ^op) SetCat@{u h _ _ _ _ _}) 2%nat
  := @local_horn2_resp _ _ T (VtxCat_IsGpd T) A B E fin_first.

Definition high_eq_local_horn (A B E : Y)
  : Horn2S (VtxCat S) A B E (fin_next (fin_next fin_first)) →r
      (Nᵥ(S) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2%nat
  := @local_horn2_resp _ _ S (VtxCat_IsGpd S)
      A B E (fin_next (fin_next fin_first)).

(** Actual horn maps admit the selected groupoid fillings at either
    ordering of carrier and equality sizes. *)

Definition low_eq_actual_horn (i : Ordinal 2%nat)
  : HasHornFillers (Nᵥ(T) : Fct (Δ^op) SetCat@{u h _ _ _ _ _}) 2%nat i
  := vertex_gpd_horn2_HasFillers T (HC := VtxCat_IsGpd T) i.

Definition high_eq_actual_horn (i : Ordinal 2%nat)
  : HasHornFillers (Nᵥ(S) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2%nat i
  := vertex_gpd_horn2_HasFillers S (HC := VtxCat_IsGpd S) i.

(** The all-dimensional Kan structures retain both strict orderings of
    value carrier and equality universes. *)

Definition low_eq_vertex_kan
  : HasKanFillers (Nᵥ(T) : Fct (Δ^op) SetCat@{u h _ _ _ _ _})
  := vertex_gpd_HasKanFillers T (HC := VtxCat_IsGpd T).

Definition high_eq_vertex_kan
  : HasKanFillers (Nᵥ(S) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  := vertex_gpd_HasKanFillers S (HC := VtxCat_IsGpd S).

End VertexNerveLevels.

(** Boundary and horn carriers retain factorization witnesses, while their
    specified equality may lie strictly below or above the value carrier. *)

Section SimplicialBoundaryLevels.
Universes e u p.
Constraint e < u.
Constraint u < p.

Definition low_eq_boundary (n : nat)
  : Fct (Δ^op) SetCat@{u e _ _ _ _ _}
  := ∂Δ[n].

Definition high_eq_horn (n : nat) (i : Ordinal n)
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Λ[n; i].

Definition low_eq_horn_restriction
    (X : Fct (Δ^op) SetCat@{u e _ _ _ _ _})
    (n : nat) (i : Ordinal n)
  : X n →r HornS X n i
  := horn_restrict_resp i.

Definition high_eq_horn_matching
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
    (n : nat) (i : Ordinal n)
  : SetC
  := HornS X n i.
End SimplicialBoundaryLevels.

(** Matching isomorphisms lift their native data into common sizes while
    allowing either ordering of the presheaf's own value sizes. *)

Section SimplicialMatchingLevels.
Universes e u p v q.
Constraint e < u.
Constraint u < p.
Constraint p < v.
Constraint v < q.
Context (X : Fct (Δ^op) SetCat@{u e _ _ _ _ _})
    (Y : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

Definition low_eq_matching (n : nat) (i : Ordinal (S n))
  : LiftS@{_ _ v q} (HornMatchingS X n i) ≅[SetCat]
      LiftS@{_ _ v q} (HornS X (S n) i)
  := horn_matching_iso (X := X) n i.

Definition high_eq_matching (n : nat) (i : Ordinal (S n))
  : LiftS@{_ _ v q} (HornMatchingS Y n i) ≅[SetCat]
      LiftS@{_ _ v q} (HornS Y (S n) i)
  := horn_matching_iso (X := Y) n i.

(** Boundary restriction becomes an isomorphism only after the ordinary
    inclusion into common sizes; coskeletal filling itself stays native. *)

Context `{HX : !IsCoskeletal X 2%nat} `{HY : !IsCoskeletal Y 2%nat}.

Definition low_eq_coskeletal_boundary (n : nat)
  : LiftS@{_ _ v q} (X (S (2 + n))) ≅[SetCat]
      LiftS@{_ _ v q} (BoundaryS X (S (2 + n)))
  := coskeletal_boundary_iso n.

Definition high_eq_coskeletal_boundary (n : nat)
  : LiftS@{_ _ v q} (Y (S (2 + n))) ≅[SetCat]
      LiftS@{_ _ v q} (BoundaryS Y (S (2 + n)))
  := coskeletal_boundary_iso n.
End SimplicialMatchingLevels.

From Cats Require Import
  Cat.Monad.Monoid.

(** Monoid and monad hom equalities retain either ordering of the native
    morphism and equality levels. Stored law witnesses may enlarge the
    hom carrier, but must not force its equality level upward. *)

Section MonoidalLevels.
Universes o e h p.
Constraint o < e.
Constraint e < h.
Constraint h < p.
Context (C0 : Cat@{o h e _ _}) (C1 : Cat@{o h p _ _})
    (MC0 : HasMonoidal C0) (MC1 : HasMonoidal C1).

Definition low_eq_monoid_category
  : Cat@{_ _ e _ _}
  := MonoidCat C0.

Definition high_eq_monoid_category
  : Cat@{_ _ p _ _}
  := MonoidCat C1.

Definition low_eq_monad_category
  : Cat@{_ _ e _ _}
  := MonadCat C0.

Definition high_eq_monad_category
  : Cat@{_ _ p _ _}
  := MonadCat C1.

(** The correspondence also instantiates at both strict universe orders. *)

Definition low_eq_monad_monoid_equiv
  : low_eq_monad_category ≃C (@MonoidCat _ (EndofctMonoidal C0))
  := monad_monoid_equiv C0.

Definition high_eq_monad_monoid_equiv
  : high_eq_monad_category ≃C (@MonoidCat _ (EndofctMonoidal C1))
  := monad_monoid_equiv C1.
End MonoidalLevels.

(** Monoid objects can live strictly below or above the bound of the
    chosen monoidal structure on the same category. *)

Section MonoidObjectLevels.
Universes lo chosen hi.
Constraint lo < chosen.
Constraint chosen < hi.
Context (C : Cat) `{MC : !HasMonoidal@{_ _ _ _ chosen _ _ _} C}.

Definition monoid_objects_below_choice
  : Cat@{lo _ _ _ _}
  := MonoidCat C.

Definition monoid_objects_above_choice
  : Cat@{hi _ _ _ _}
  := MonoidCat C.
End MonoidObjectLevels.

From Cats Require Import
  Cat.Comma.Arrow
  Cat.Comma.Slice
  Cat.FreeObject.Adjunction.

(** Square witnesses may live above side-map equalities; neither comma
    equality nor the free-object adjunction identifies native hom sizes. *)

Section CommaFreeLevels.
Universes o e h p.
Constraint o < e.
Constraint e < h.
Constraint h < p.
Context (A B : Cat@{o h e _ _}) (D : Cat@{o h p _ _})
    (F : Fct A D) (G : Fct B D).

Definition comma_low_side_equality
  : Cat@{_ _ e _ _}
  := F ↓C G.

Context (U : Fct D A) `{HF : !HasFreeObj U}.

Definition mixed_free_adj
  : FreeFct U ⊣ U
  := FreeAdj U.

Definition mixed_free_monad
  : Monad A
  := FreeMonad U.
End CommaFreeLevels.

From Cats Require Import
  Cat.FreeObject.Representable.

(** Pointwise representation lifts each native hom family independently.
    Source hom equality and representing hom equality are strictly different. *)

Section FreeRepresentationLevels.
Universes o e h p v q.
Constraint o < e.
Constraint e < h.
Constraint h < p.
Constraint p < v.
Constraint v < q.
Context (C : Cat@{o h e _ _}) (D : Cat@{o h p _ _})
    (U : Fct D C) `{HF : !HasFreeObj U} (X : @Ob C).

Definition mixed_free_representation
  : FreeOb U X ⦂ Rep↑
      (FreeHomF U X : Fct D SetCat@{v q _ _ _ _ _})
  := universal_arrow_representation U (free_universal U X).

(** A second model separates the native hom carriers as well. *)

Context (E : Cat@{o p h _ _}) (V : Fct E C)
    `{HV : !HasFreeObj V}.

Definition mixed_free_carrier_representation
  : FreeOb V X ⦂ Rep↑
      (FreeHomF V X : Fct E SetCat@{v q _ _ _ _ _})
  := universal_arrow_representation V (free_universal V X).
End FreeRepresentationLevels.

From Cats Require Import
  Cat.Monoidal.Constant
  Cat.Monoidal.Transport.

(** Lax transport works in both directions between categories whose hom
    equalities have opposite strict size orders relative to their carriers.
    The target equality must retain its own size after mapping monoids. *)

Section LaxMonoidalLevels.
Universes o e h p.
Constraint o < e.
Constraint e < h.
Constraint h < p.
Context (C0 : Cat@{o h e _ _}) (C1 : Cat@{o h p _ _})
    (MC0 : HasMonoidal C0) (MC1 : HasMonoidal C1)
    (L01 : LaxMonoidalFct C0 C1)
    (L10 : LaxMonoidalFct C1 C0).

(** Coercion recovers the underlying functor at either native equality size. *)

Definition low_eq_lax_underlying
  : Fct C1 C0
  := L10.

Definition high_eq_lax_underlying
  : Fct C0 C1
  := L01.

Definition low_eq_lax_monoid_fct
  : Fct (MonoidCat C1) (MonoidCat C0)
  := LaxMonoidF L10.

Definition high_eq_lax_monoid_fct
  : Fct (MonoidCat C0) (MonoidCat C1)
  := LaxMonoidF L01.

Definition low_eq_lax_monoid_map {A B : MonoidObj C1}
    (f g : (@Hom (MonoidCat C1)) A B)
  : Type@{e}
  := fmap low_eq_lax_monoid_fct f ≈ fmap low_eq_lax_monoid_fct g.

Definition high_eq_lax_monoid_map {A B : MonoidObj C0}
    (f g : (@Hom (MonoidCat C0)) A B)
  : Type@{p}
  := fmap high_eq_lax_monoid_fct f ≈ fmap high_eq_lax_monoid_fct g.

Definition mixed_constant_lax (A : MonoidObj C0)
  : LaxMonoidalFct C1 C0
  := ConstLaxMonoidalF A.
End LaxMonoidalLevels.

(** Restriction compares bases naturally while retaining independent hom
    and equality levels in the base and in both interpreting categories.
    Auxiliary law bounds stay strictly above those levels. *)

Section RestrictionLevels.
Universes o h p a b l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < l.
Constraint l < o.
Context (B : Cat@{o h p l l}) (B' : Cat@{o p h l l})
    (E : Cat@{o a b l l}) (D : Cat@{o b a l l}).
Context (P T : Fct E B) (Q : Fct D B) (S : Fct D E)
    (β : (P ∘F S) ≅N Q) (π : T ⇒ P)
    (Hπ : is_comprehension π)
    (HS : ∀ X Y (f : (@Hom D) X Y),
      f ⦂ Cart(Q) → (fmap S f) ⦂ Cart(P)) (HQ : HasCartLift Q).
Definition high_eq_restricted_projection
  : (T ∘F S) ⇒ Q
  := ComprehensionRestrictionN S β π.
Definition high_eq_restricted_universal
  : is_comprehension high_eq_restricted_projection
  := comprehension_restrict_universal S β π Hπ HS.
Definition high_eq_restricted_comprehension
  : Comprehension Q
  := RestrictedComprehension S β π Hπ HS HQ.
Definition high_eq_restricted_hom_equality {X Y : @Ob D}
    (f g : Hom X Y)
  : Type@{p}
  := fmap (ExtF high_eq_restricted_comprehension) f ≈
      fmap (ExtF high_eq_restricted_comprehension) g.
Context (P' T' : Fct D B') (Q' : Fct E B') (S' : Fct E D)
    (β' : (P' ∘F S') ≅N Q') (π' : T' ⇒ P')
    (Hπ' : is_comprehension π')
    (HS' : ∀ X Y (f : (@Hom E) X Y),
      f ⦂ Cart(Q') → (fmap S' f) ⦂ Cart(P')) (HQ' : HasCartLift Q').
Definition low_eq_restricted_projection
  : (T' ∘F S') ⇒ Q'
  := ComprehensionRestrictionN S' β' π'.
Definition low_eq_restricted_universal
  : is_comprehension low_eq_restricted_projection
  := comprehension_restrict_universal S' β' π' Hπ' HS'.
Definition low_eq_restricted_comprehension
  : Comprehension Q'
  := RestrictedComprehension S' β' π' Hπ' HS' HQ'.
Definition low_eq_restricted_hom_equality {X Y : @Ob E}
    (f g : Hom X Y)
  : Type@{h}
  := fmap (ExtF low_eq_restricted_comprehension) f ≈
      fmap (ExtF low_eq_restricted_comprehension) g.
End RestrictionLevels.

From Cats Require Import
  DTT.Display.Interpretation.

(** Type elements may be larger than the base laws and are interpreted in
    categories with independently larger hom/equality levels. Recovery keeps
    the original base hom bounds for terms in both strict size orders. *)

Section InterpretedElementLevels.
Universes o h p l a b.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint l < a.
Constraint a < b.
Constraint b < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l})
    (E : Cat@{o a b o o}) (E' : Cat@{o b a o o})
    (A : Fct (C^op) SetCat@{a b _ _ _ _ _})
    (A' : Fct (D^op) SetCat@{b a _ _ _ _ _}).
Context (P T : Fct E C) (S : Fct (ElementsCat A) E)
    (β : (P ∘F S) ≅N ElementsBaseF A)
    (π : T ⇒ P) (Hπ : is_comprehension π)
    (HS : ∀ X Y (f : ElementMap A X Y), (fmap S f) ⦂ Cart(P)).
Definition high_eq_interpreted_comprehension
  : Comprehension (ElementsBaseF A)
  := InterpretedElementsComprehension A S β π Hπ HS.
Definition high_eq_interpreted_display
  : HasDisplay C A
  := InterpretedElements_HasDisplay A S β π Hπ HS.
Definition high_eq_interpreted_terms (HT : HasTerminal C)
    (Γ : @Ob C) (X : A Γ)
  : SetC@{p p}
  := Tm (@InterpretedCwF C E A P T S β π Hπ HS HT) Γ X.
Definition high_eq_interpreted_comparison
  : @DisplayElementsF C A high_eq_interpreted_display ≅N (T ∘F S)
  := interpreted_display_iso A S β π Hπ HS.
Context (P' T' : Fct E' D) (S' : Fct (ElementsCat A') E')
    (β' : (P' ∘F S') ≅N ElementsBaseF A')
    (π' : T' ⇒ P') (Hπ' : is_comprehension π')
    (HS' : ∀ X Y (f : ElementMap A' X Y), (fmap S' f) ⦂ Cart(P')).
Definition low_eq_interpreted_comprehension
  : Comprehension (ElementsBaseF A')
  := InterpretedElementsComprehension A' S' β' π' Hπ' HS'.
Definition low_eq_interpreted_display
  : HasDisplay D A'
  := InterpretedElements_HasDisplay A' S' β' π' Hπ' HS'.
Definition low_eq_interpreted_terms (HT : HasTerminal D)
    (Γ : @Ob D) (X : A' Γ)
  : SetC@{p h}
  := Tm (@InterpretedCwF D E' A' P' T' S' β' π' Hπ' HS' HT) Γ X.
Definition low_eq_interpreted_comparison
  : @DisplayElementsF D A' low_eq_interpreted_display ≅N (T' ∘F S')
  := interpreted_display_iso A' S' β' π' Hπ' HS'.
End InterpretedElementLevels.

(** General pairing laws must retain independent type/term sizes strictly
    above context homs. Fix the input FamCat universes explicitly, and check
    the context-display and comprehension clients in both strict orders. *)

Section GeneralPairingLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l})
    (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _})
    (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition high_eq_pairing_composition
  := @context_pair_comp C T HC.
Definition low_eq_pairing_composition
  := @context_pair_comp D U HU.
Definition high_eq_pairing_injectivity
  := @context_pair_inj C T HC.
Definition low_eq_pairing_injectivity
  := @context_pair_inj D U HU.
Definition high_eq_general_context_display
  : HasDisplay C (FamBaseF ∘F T)
  := @ContextExtension_HasDisplay C T HC.
Definition low_eq_general_context_display
  : HasDisplay D (FamBaseF ∘F U)
  := @ContextExtension_HasDisplay D U HU.
Definition high_eq_general_context_comprehension
  : Comprehension (CwFBaseF T)
  := @CwFComprehension C T HC.
Definition low_eq_general_context_comprehension
  : Comprehension (CwFBaseF U)
  := @CwFComprehension D U HU.
End GeneralPairingLevels.

From Cats Require Import
  DTT.Context.Elements.

(** Context interpretation retains independent type/term levels, with
    recovered section carriers below the law bound in both strict orders. *)

Section ContextElementLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition high_eq_original_types (Γ : @Ob C)
  : SetC@{a c}
  := Ty T Γ.
Definition high_eq_original_terms (Γ : @Ob C) (A : Ty T Γ)
  : SetC@{b d}
  := Tm T Γ A.
Definition low_eq_original_types (Γ : @Ob D)
  : SetC@{c a}
  := Ty U Γ.
Definition low_eq_original_terms (Γ : @Ob D) (A : Ty U Γ)
  : SetC@{d b}
  := Tm U Γ A.
Definition high_eq_context_interpretation
  : Fct (ElementsCat (FamBaseF ∘F T)) (ContextTypeCat T)
  := @ContextElementsF C T HC.
Definition low_eq_context_interpretation
  : Fct (ElementsCat (FamBaseF ∘F U)) (ContextTypeCat U)
  := @ContextElementsF D U HU.
Definition high_eq_context_recovered_display
  : HasDisplay C (FamBaseF ∘F T)
  := @ContextElements_HasDisplay C T HC.
Definition low_eq_context_recovered_display
  : HasDisplay D (FamBaseF ∘F U)
  := @ContextElements_HasDisplay D U HU.
Definition high_eq_context_recovered_terms (Γ : @Ob C) (A : Ty T Γ)
  : SetC@{p p}
  := @DisplayTerms C (FamBaseF ∘F T) high_eq_context_recovered_display Γ A.
Definition low_eq_context_recovered_terms (Γ : @Ob D) (A : Ty U Γ)
  : SetC@{p h}
  := @DisplayTerms D (FamBaseF ∘F U) low_eq_context_recovered_display Γ A.
Definition high_eq_context_fiber_comparison (Γ : @Ob C) (A : Ty T Γ)
  : LiftS@{_ _ d l} (Tm T Γ A) ≅[SetCat]
      LiftS@{_ _ d l} (high_eq_context_recovered_terms Γ A)
  := @context_elements_term_iso C T HC Γ A.
Definition low_eq_context_fiber_comparison (Γ : @Ob D) (A : Ty U Γ)
  : LiftS@{_ _ d l} (Tm U Γ A) ≅[SetCat]
      LiftS@{_ _ d l} (low_eq_context_recovered_terms Γ A)
  := @context_elements_term_iso D U HU Γ A.
Definition high_eq_context_total_comparison
  := @context_elements_display_iso C T HC.
Definition low_eq_context_total_comparison
  := @context_elements_display_iso D U HU.
Definition high_eq_context_recovered_cwf (HT : HasTerminal C)
  : CwF C
  := @ContextElementsCwF C T HC HT.
Definition low_eq_context_recovered_cwf (HT : HasTerminal D)
  : CwF D
  := @ContextElementsCwF D U HU HT.
End ContextElementLevels.

(** Inverse comparison laws retain explicitly larger original FamCat
    carrier/equality inputs in both hom orders, without a terminal choice. *)

Section ContextElementInverseLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition high_eq_context_inverse_square
  := @context_elements_term_square_inv C T HC.
Definition low_eq_context_inverse_square
  := @context_elements_term_square_inv D U HU.
Definition high_eq_context_inverse_conversion
  := @context_elements_term_inv_conv C T HC.
Definition low_eq_context_inverse_conversion
  := @context_elements_term_inv_conv D U HU.
Definition high_eq_context_inverse_substitution
  := @context_elements_term_inv_sub C T HC.
Definition low_eq_context_inverse_substitution
  := @context_elements_term_inv_sub D U HU.
End ContextElementInverseLevels.

From Cats Require Import
  Instance.Set.Fam.Lift.

(** Fiber lifting retains independent base, fiber and raised levels in both
    orders. Its source map bound can also exceed the target carrier bound;
    the explicit wrappers reject downward carrier or equality resizing. *)

Section IndependentFiberLift.
Universes u p a b c d l o.
Constraint Set < u.
Constraint u < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < l.
Constraint l < o.
Context (X : SetC@{u p}) (Y : SetC@{p u})
    (A : FamS@{u p l a b} X) (B : FamS@{p u l b a} Y)
    (U V : FamC@{u p l a b}) (W Z : FamC@{p u l b a}).
Definition high_eq_fiber_lift
  : FamS@{u p l c d} X
  := LiftFamS A.
Definition low_eq_fiber_lift
  : FamS@{p u l d c} Y
  := LiftFamS B.
Definition high_eq_family_lift
  : FamC@{u p l c d}
  := LiftFamC U.
Definition low_eq_family_lift
  : FamC@{p u l d c}
  := LiftFamC W.
Definition high_eq_family_map (f : FamF U V)
  : FamF (LiftFamC U : FamC@{u p l c d})
      (LiftFamC V : FamC@{u p l c d})
  := lift_fam_map f.
Definition low_eq_family_map (f : FamF W Z)
  : FamF (LiftFamC W : FamC@{p u l d c})
      (LiftFamC Z : FamC@{p u l d c})
  := lift_fam_map f.
Definition high_eq_family_fct
  : Fct FamCat@{o l l o l u p l a b l l l l l l}
      FamCat@{o l l o l u p l c d l l l l l l}
  := FamLiftF.
Definition low_eq_family_fct
  : Fct FamCat@{o l l o l p u l b a l l l l l l}
      FamCat@{o l l o l p u l d c l l l l l l}
  := FamLiftF.
Definition high_eq_base_comparison
  : (FamBaseF ∘F high_eq_family_fct) ⇒ FamBaseF
  := FamLiftBaseN.
Definition low_eq_base_comparison
  : (FamBaseF ∘F low_eq_family_fct) ⇒ FamBaseF
  := FamLiftBaseN.
Definition high_eq_base_iso
  : (FamBaseF ∘F high_eq_family_fct) ≅N FamBaseF
  := fam_lift_base_iso.
Definition low_eq_base_iso
  : (FamBaseF ∘F low_eq_family_fct) ≅N FamBaseF
  := fam_lift_base_iso.
Definition high_aux_family_map
    (f : FamF@{_ _ _ _ _ _ _ _ l _ _ _ _ _} U V)
  : FamF (LiftFamC U : FamC@{u p l c d})
      (LiftFamC V : FamC@{u p l c d})
  := lift_fam_map f.
Definition low_aux_family_map
    (f : FamF@{_ _ _ _ _ _ _ _ l _ _ _ _ _} W Z)
  : FamF (LiftFamC W : FamC@{p u l d c})
      (LiftFamC Z : FamC@{p u l d c})
  := lift_fam_map f.
Fail Definition bad_high_carrier
  : FamS@{u p l u d} X
  := LiftFamS A.
Fail Definition bad_high_equality
  : FamS@{u p l c p} X
  := LiftFamS A.
Fail Definition bad_low_carrier
  : FamS@{p u l p c} Y
  := LiftFamS B.
Fail Definition bad_low_equality
  : FamS@{p u l d u} Y
  := LiftFamS B.
End IndependentFiberLift.

From Cats Require Import
  DTT.Context.Comparison.

(** The original and recovered type-and-term functors compare after raising
    only their fibers. Fix the original type bases strictly above the common
    fiber bounds, in both hom orders, with independent auxiliary law bounds. *)

Section RaisedFibersBelowTypes.
Universes o h p a b c d e f l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < e.
Constraint e < f.
Constraint f < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ e f _ a b _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ f e _ b a _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition high_type_forward_fiber Γ
  : (LiftFamS (Tm T Γ) : FamS@{e f l c d} (Ty T Γ)) →Fam
      (LiftFamS (@DisplayTerms C (FamBaseF ∘F T)
        (@ContextElements_HasDisplay C T HC) Γ)
        : FamS@{e f l c d} (Ty T Γ))
  := @ContextElementsFiberMap C T HC Γ.
Definition low_type_forward_fiber Γ
  : (LiftFamS (Tm U Γ) : FamS@{f e l d c} (Ty U Γ)) →Fam
      (LiftFamS (@DisplayTerms D (FamBaseF ∘F U)
        (@ContextElements_HasDisplay D U HU) Γ)
        : FamS@{f e l d c} (Ty U Γ))
  := @ContextElementsFiberMap D U HU Γ.
Definition high_type_backward_fiber Γ
  : (LiftFamS (@DisplayTerms C (FamBaseF ∘F T)
        (@ContextElements_HasDisplay C T HC) Γ)
        : FamS@{e f l c d} (Ty T Γ)) →Fam
      (LiftFamS (Tm T Γ) : FamS@{e f l c d} (Ty T Γ))
  := @ContextElementsFiberInvMap C T HC Γ.
Definition low_type_backward_fiber Γ
  : (LiftFamS (@DisplayTerms D (FamBaseF ∘F U)
        (@ContextElements_HasDisplay D U HU) Γ)
        : FamS@{f e l d c} (Ty U Γ)) →Fam
      (LiftFamS (Tm U Γ) : FamS@{f e l d c} (Ty U Γ))
  := @ContextElementsFiberInvMap D U HU Γ.
Definition high_type_forward
  : ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ e f _ c d _ _ _ _ _ _}) ∘F T)
      ⇒ ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ e f _ c d _ _ _ _ _ _})
        ∘F @DisplayTyTmF C (FamBaseF ∘F T)
          (@ContextElements_HasDisplay C T HC))
  := @ContextElementsTyTmN C T HC.
Definition low_type_forward
  : ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ f e _ d c _ _ _ _ _ _}) ∘F U)
      ⇒ ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ f e _ d c _ _ _ _ _ _})
        ∘F @DisplayTyTmF D (FamBaseF ∘F U)
          (@ContextElements_HasDisplay D U HU))
  := @ContextElementsTyTmN D U HU.
Definition high_type_iso
  : ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ e f _ c d _ _ _ _ _ _}) ∘F T)
      ≅N ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ e f _ c d _ _ _ _ _ _})
        ∘F @DisplayTyTmF C (FamBaseF ∘F T)
          (@ContextElements_HasDisplay C T HC))
  := @context_elements_ty_tm_iso C T HC.
Definition low_type_iso
  : ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ f e _ d c _ _ _ _ _ _}) ∘F U)
      ≅N ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ f e _ d c _ _ _ _ _ _})
        ∘F @DisplayTyTmF D (FamBaseF ∘F U)
          (@ContextElements_HasDisplay D U HU))
  := @context_elements_ty_tm_iso D U HU.
Definition high_type_inverse
  : ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ e f _ c d _ _ _ _ _ _})
        ∘F @DisplayTyTmF C (FamBaseF ∘F T)
          (@ContextElements_HasDisplay C T HC))
      ⇒ ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ e f _ c d _ _ _ _ _ _}) ∘F T)
  := @ContextElementsTyTmInvN C T HC.
Definition low_type_inverse
  : ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ f e _ d c _ _ _ _ _ _})
        ∘F @DisplayTyTmF D (FamBaseF ∘F U)
          (@ContextElements_HasDisplay D U HU))
      ⇒ ((FamLiftF : Fct _ FamCat@{_ _ _ _ _ f e _ d c _ _ _ _ _ _}) ∘F U)
  := @ContextElementsTyTmInvN D U HU.
Definition high_type_fiber_iso Γ
  : @is_iso (FamSCat (Ty T Γ)) _ _ (high_type_forward_fiber Γ)
  := @context_elements_fiber_map_iso C T HC Γ.
Definition low_type_fiber_iso Γ
  : @is_iso (FamSCat (Ty U Γ)) _ _ (low_type_forward_fiber Γ)
  := @context_elements_fiber_map_iso D U HU Γ.
End RaisedFibersBelowTypes.

From Cats Require Import
  DTT.Context.Section.

(** The section/pairing laws retain fixed original type and term bounds
    above both context hom levels, in both orders. *)

Section ContextSectionPairingLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition high_eq_lift_term_section
  := @context_lift_term_section C T HC.
Definition low_eq_lift_term_section
  := @context_lift_term_section D U HU.
Definition high_eq_lift_section_term
  := @context_lift_section_term C T HC.
Definition low_eq_lift_section_term
  := @context_lift_section_term D U HU.
End ContextSectionPairingLevels.

From Cats Require Import
  DTT.Context.Elements.

(** Canonical pairing and generic-term comparisons retain fixed original
    type/term bounds strictly above both context hom levels, in both orders. *)

Section CanonicalPairingLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition high_eq_canonical_projection
  := @context_elements_context_proj C T HC.
Definition low_eq_canonical_projection
  := @context_elements_context_proj D U HU.
Definition high_eq_canonical_pair
  := @context_elements_pair C T HC.
Definition low_eq_canonical_pair
  := @context_elements_pair D U HU.
Definition high_eq_canonical_pair_inv
  := @context_elements_pair_inv C T HC.
Definition low_eq_canonical_pair_inv
  := @context_elements_pair_inv D U HU.
Definition high_eq_canonical_var
  := @context_elements_var C T HC.
Definition low_eq_canonical_var
  := @context_elements_var D U HU.
Definition high_eq_canonical_var_inv
  := @context_elements_var_inv C T HC.
Definition low_eq_canonical_var_inv
  := @context_elements_var_inv D U HU.
End CanonicalPairingLevels.

(** Derived context operations preserve fixed type sizes above both hom
    levels, in both orders, with independent bounds for the laws. *)

Section DisplayContextActionLevels.
Universes o h p a b l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (P : Fct (C^op) SetCat@{a b _ _ _ _ _})
    (Q : Fct (D^op) SetCat@{b a _ _ _ _ _}).
Context (HP : HasDisplay C P) (HQ : HasDisplay D Q).
Definition high_eq_display_context_action_terms (Γ : @Ob C) (A : P Γ)
  : SetC@{p p}
  := @DisplayTerms C P HP Γ A.
Definition low_eq_display_context_action_terms (Γ : @Ob D) (A : Q Γ)
  : SetC@{p h}
  := @DisplayTerms D Q HQ Γ A.
Definition high_eq_display_context_conv
  := @display_context_conv C P HP.
Definition low_eq_display_context_conv
  := @display_context_conv D Q HQ.
Definition high_eq_display_context_lift
  := @display_context_lift C P HP.
Definition low_eq_display_context_lift
  := @display_context_lift D Q HQ.
End DisplayContextActionLevels.

(** Type carrier and equality bounds may also lie above the auxiliary
    bounds of the base-category laws. Keep the same recovered term bounds. *)

Section DisplayContextActionLargeTypeLevels.
Universes o h p a b l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint a < b.
Constraint l < a.
Constraint b < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (P : Fct (C^op) SetCat@{a b _ _ _ _ _})
    (Q : Fct (D^op) SetCat@{b a _ _ _ _ _}).
Context (HP : HasDisplay C P) (HQ : HasDisplay D Q).
Definition large_type_high_eq_display_terms (Γ : @Ob C) (A : P Γ)
  : SetC@{p p}
  := @DisplayTerms C P HP Γ A.
Definition large_type_low_eq_display_terms (Γ : @Ob D) (A : Q Γ)
  : SetC@{p h}
  := @DisplayTerms D Q HQ Γ A.
Definition large_type_high_eq_display_context_conv
  := @display_context_conv C P HP.
Definition large_type_low_eq_display_context_conv
  := @display_context_conv D Q HQ.
Definition large_type_high_eq_display_context_lift
  := @display_context_lift C P HP.
Definition large_type_low_eq_display_context_lift
  := @display_context_lift D Q HQ.
End DisplayContextActionLargeTypeLevels.

(** Canonical context operations retain fixed original type/term sizes
    above both hom levels. Recovered terms keep their original hom bounds. *)

Section CanonicalContextActionLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition canonical_action_high_eq_context_conv
  := @context_elements_context_conv C T HC.
Definition canonical_action_low_eq_context_conv
  := @context_elements_context_conv D U HU.
Definition canonical_action_high_eq_context_lift
  := @context_elements_context_lift C T HC.
Definition canonical_action_low_eq_context_lift
  := @context_elements_context_lift D U HU.
Definition canonical_action_high_eq_terms (Γ : @Ob C) (A : Ty T Γ)
  : SetC@{p p}
  := @DisplayTerms C (FamBaseF ∘F T)
      (@ContextElements_HasDisplay C T HC) Γ A.
Definition canonical_action_low_eq_terms (Γ : @Ob D) (A : Ty U Γ)
  : SetC@{p h}
  := @DisplayTerms D (FamBaseF ∘F U)
      (@ContextElements_HasDisplay D U HU) Γ A.
End CanonicalContextActionLevels.

(** Original type and term bounds may independently exceed the auxiliary
    bounds of the base-category laws in both hom orders. *)

Section CanonicalContextActionLargeInputLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint l < a.
Constraint d < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition canonical_large_action_high_eq_context_conv
  := @context_elements_context_conv C T HC.
Definition canonical_large_action_low_eq_context_conv
  := @context_elements_context_conv D U HU.
Definition canonical_large_action_high_eq_context_lift
  := @context_elements_context_lift C T HC.
Definition canonical_large_action_low_eq_context_lift
  := @context_elements_context_lift D U HU.
Definition canonical_large_action_high_eq_terms (Γ : @Ob C) (A : Ty T Γ)
  : SetC@{p p}
  := @DisplayTerms C (FamBaseF ∘F T)
      (@ContextElements_HasDisplay C T HC) Γ A.
Definition canonical_large_action_low_eq_terms (Γ : @Ob D) (A : Ty U Γ)
  : SetC@{p h}
  := @DisplayTerms D (FamBaseF ∘F U)
      (@ContextElements_HasDisplay D U HU) Γ A.
End CanonicalContextActionLargeInputLevels.

(** Canonical cone transport and factor comparison retain fixed original
    type/term sizes above both hom levels. *)

Section CanonicalPullbackFactorLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < l.
Constraint l < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition canonical_factor_high_eq_cone
  := @context_elements_lift_cone C T HC.
Definition canonical_factor_low_eq_cone
  := @context_elements_lift_cone D U HU.
Definition canonical_factor_high_eq_mediator
  := @context_elements_context_factor C T HC.
Definition canonical_factor_low_eq_mediator
  := @context_elements_context_factor D U HU.
End CanonicalPullbackFactorLevels.

(** Original type and term bounds may independently exceed the auxiliary
    bounds of the base-category laws in both hom orders. *)

Section CanonicalPullbackFactorLargeInputLevels.
Universes o h p a b c d l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint l < a.
Constraint d < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
    (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (HU : HasContextExtension U).
Definition canonical_large_factor_high_eq_cone
  := @context_elements_lift_cone C T HC.
Definition canonical_large_factor_low_eq_cone
  := @context_elements_lift_cone D U HU.
Definition canonical_large_factor_high_eq_mediator
  := @context_elements_context_factor C T HC.
Definition canonical_large_factor_low_eq_mediator
  := @context_elements_context_factor D U HU.
End CanonicalPullbackFactorLargeInputLevels.
