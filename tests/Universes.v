From Cats Require Import STLC.Free.
From Cats Require Import
  Cat.Shape.Simplex.Core
  Instance.Set.Simplicial.Nerve
  Instance.Set.Simplicial.Monoid
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
  Cat.Functor.Closed
  Cat.Natural
  Cat.Bicategory.Core
  Cat.Bicategory.Thin.
From Cats Require Import Cat.CCC.
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
From Cats Require Import DTT.Display.Section.
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

(** 具体广集模型在可行时保持层级独立。选定等化子需要 [p ≤ u]，生成余等化子
    需要 [u ≤ p]；这些界属于当前模型，而非抽象接口。 *)

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

(** 形状中的大关系见证不会增大两种模型所需的索引载体。 *)

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
    (HG : HasFiniteGenerators K).

(** Finite covers and generators bypass the larger raw shape carriers. *)

(** 有限覆盖及生成元允许绕过形状原始载体的更大层级。 *)

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

(** 基础广集及其范畴接受载体与相等见证的两种大小排列。 *)

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

(** 构造实例化一般 [Cat] 时，不得等同态射与相等见证宇宙；两种排列均需检查。 *)

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
  := Fct C C.
Definition low_eq_functors
  := Fct D D.
Definition high_eq_ccc
  := CCC C.
Definition low_eq_ccc
  := CCC D.
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
End CategoryLevels.

(** Transposition must preserve hom/equality levels in either ordering.
    The ambient set category for the correspondence must not identify them. *)

(** 转置必须保留 Hom 与相等层级的两种排列，所用环境集合范畴不得将它们等同。 *)

Section ExponentialLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context `{HC : !CCC C} `{HD : !CCC D}.

Definition high_eq_curry (X Y Z : @Ob C)
  : HomSet (Z × X) Y →r HomSet Z (Y ^ X)
  := exponential_curry_resp.
Definition low_eq_curry (X Y Z : @Ob D)
  : HomSet (Z × X) Y →r HomSet Z (Y ^ X)
  := exponential_curry_resp.
Definition high_eq_uncurry (X Y Z : @Ob C)
  : HomSet Z (Y ^ X) →r HomSet (Z × X) Y
  := exponential_uncurry_resp.
Definition low_eq_uncurry (X Y Z : @Ob D)
  : HomSet Z (Y ^ X) →r HomSet (Z × X) Y
  := exponential_uncurry_resp.
Definition high_eq_exponential_hom (X Y Z : @Ob C)
  : HomSet (Z × X) Y ≅[SetCat@{h p _ _ _ _ _}] HomSet Z (Y ^ X)
  := exponential_hom_iso.
Definition low_eq_exponential_hom (X Y Z : @Ob D)
  : HomSet (Z × X) Y ≅[SetCat@{p h _ _ _ _ _}] HomSet Z (Y ^ X)
  := exponential_hom_iso.
Definition high_eq_exponential_adjunction (X : @Ob C)
  : (-× X) ⊣ (-^ X)
  := ProductExponentialAdjunction X.
Definition low_eq_exponential_adjunction (X : @Ob D)
  : (-× X) ⊣ (-^ X)
  := ProductExponentialAdjunction X.
Definition high_eq_exponential_nat (X : @Ob C)
  : @NatIso _ SetCat@{h p _ _ _ _ _} (LeftHomF (-× X)) (RightHomF (-^ X))
  := exponential_hom_nat_iso X.
Definition low_eq_exponential_nat (X : @Ob D)
  : @NatIso _ SetCat@{p h _ _ _ _ _} (LeftHomF (-× X)) (RightHomF (-^ X))
  := exponential_hom_nat_iso X.
Definition high_eq_exponential_bifunctor
  : Functor (C^op ×C C) C
  := (-^-).
Definition low_eq_exponential_bifunctor
  : Functor (D^op ×C D) D
  := (-^-).
Definition high_eq_contravariant_exponential (Y : @Ob C)
  : Functor (C^op) C
  := (Y ^-).
Definition low_eq_contravariant_exponential (Y : @Ob D)
  : Functor (D^op) D
  := (Y ^-).
Definition high_eq_fixed_exponential (X : @Ob C)
  : π2F (-^-) X ≅N (-^ X)
  := exponential_fixed_nat_iso X.
Definition low_eq_fixed_exponential (X : @Ob D)
  : π2F (-^-) X ≅N (-^ X)
  := exponential_fixed_nat_iso X.
(** Structural isomorphisms keep the two hom/equality orderings distinct. *)

(** 结构同构保持两种 Hom／相等层级排列的分离。 *)

Definition high_eq_exponential_laws (X Y Z : @Ob C)
  : (((X × Y) ^ Z) ≅ ((X ^ Z) × (Y ^ Z))) ∧
      (((Y ^ X) ^ Z) ≅ (Y ^ (X × Z))) ∧ ((Y ^ 1) ≅ Y) ∧ ((1 ^ X) ≅ 1)
  := (exponential_product_iso Z X Y,
      (exponential_iterated_iso X Z Y,
        (exponential_unit_iso Y, exponential_terminal_iso X))).
Definition low_eq_exponential_laws (X Y Z : @Ob D)
  : (((X × Y) ^ Z) ≅ ((X ^ Z) × (Y ^ Z))) ∧
      (((Y ^ X) ^ Z) ≅ (Y ^ (X × Z))) ∧ ((Y ^ 1) ≅ Y) ∧ ((1 ^ X) ≅ 1)
  := (exponential_product_iso Z X Y,
      (exponential_iterated_iso X Z Y,
        (exponential_unit_iso Y, exponential_terminal_iso X))).
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
  := exponential_iterated_hom_iso X Z Y W.
Definition low_eq_iterated_hom (X Y Z W : @Ob D)
  : HomSet W ((Y ^ X) ^ Z) ≅[SetCat@{p h _ _ _ _ _}]
      HomSet W (Y ^ (X × Z))
  := exponential_iterated_hom_iso X Z Y W.

(** Public notation survives section closure and imports. *)

(** 公共记号在节结束并导入后仍然可用。 *)

Definition high_eq_internal_unit (X Y Z : @Ob C) (f : Hom Z (Y ^ X))
  : idᴱ[Y] ∘ᴱ f ≈ f
  := exponential_comp_id_l f.
Definition low_eq_double_curry (A B Y Z : @Ob D)
    (f : Hom (Z × (A × B)) Y)
  : (ƛ₂ f)^♭₂ ≈ f
  := exponential_curry_twice_β f.

Context (F : Functor C D) (G : Functor D C)
    (HF : IsCCCF F HC HD) (HG : IsCCCF G HD HC).

(** CCC-preservation composition permits different hom/equality orderings
    in its intermediate category. *)

(** CCC 保持性的复合允许中间范畴具有不同的 Hom／相等层级排列。 *)

Definition mixed_levels_closed_composite
  : IsCCCF (G ∘F F) HC HC
  := CompF_IsCCCF F G HC HD HC HF HG.

Universe s.
Constraint l < s.
Context (J : Cat@{s s s _ _}).

(** Limit preservation does not impose an indexing bound on the shape. *)

(** 极限保持性不对形状施加索引大小界。 *)

Definition high_eq_exponential_limit (A : @Ob C)
    (K : Functor J C) (L : @Ob C) (κ : L ⇒Δ K) (H : is_limit κ)
  : is_limit (MapCone (-^ A) κ)
  := exponential_preserves_limit A H.
Definition low_eq_exponential_limit (A : @Ob D)
    (K : Functor J D) (L : @Ob D) (κ : L ⇒Δ K) (H : is_limit κ)
  : is_limit (MapCone (-^ A) κ)
  := exponential_preserves_limit A H.
End ExponentialLevels.

(** An adjunction can relate categories whose two hom levels are reversed.
    Its natural hom isomorphism uses a larger ambient set category, with
    either ordering of carrier and equality-witness levels. *)

(** 伴随可关联 Hom 两个层级顺序相反的范畴；自然 Hom 同构使用更大的环境集合范畴，并接受载体与相等见证的两种排列。 *)

Section AdjunctionLevels.
Universe o h p n e l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < e.
Constraint e < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (F : Functor C D) (G : Functor D C) (A : F ⊣ G).

Definition mixed_adjunct (X : @Ob C) (Y : @Ob D)
  : HomSet (F X) Y →r HomSet X (G Y)
  := adjunct_resp A.
Definition mixed_unadjunct (X : @Ob C) (Y : @Ob D)
  : HomSet X (G Y) →r HomSet (F X) Y
  := unadjunct_resp A.
Definition mixed_adjunction_comp
  : (F ∘F IdF) ⊣ (IdF ∘F G)
  := CompAdjunction A (IdAdjunction C).
Definition high_eq_adjunction_hom
  : @NatIso _ SetCat@{n e _ _ _ _ _} (LeftHomF F) (RightHomF G)
  := adjunction_hom_nat_iso A.
Definition low_eq_adjunction_hom
  : @NatIso _ SetCat@{e n _ _ _ _ _} (LeftHomF F) (RightHomF G)
  := adjunction_hom_nat_iso A.
End AdjunctionLevels.

(** Large diagram shapes may raise cone and law levels, without identifying
    the target category's native hom and equality-witness levels. *)

(** 大图式形状可提高锥与定律的层级，但不得等同目标范畴原生的 Hom 及相等见证层级。 *)

Section LimitLevels.
Universe o h p n l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < l.
Context (J : Cat@{n h p l l}).
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context `{HC : !HasLimitsOfShape C J} `{HD : !HasLimitsOfShape D J}.

Definition high_eq_limit_functor
  := @LimitF J C HC.
Definition low_eq_limit_functor
  := @LimitF J D HD.
Definition high_eq_limit_adjunction
  := @LimitAdjunction J C HC.
Definition low_eq_limit_adjunction
  := @LimitAdjunction J D HD.
Definition high_eq_limit_converse
  := limits_iff_diagonal_right_adjoint J C.
Definition low_eq_limit_converse
  := limits_iff_diagonal_right_adjoint J D.
Definition high_eq_cone_category (K : Functor J C)
  := ConeCat K.
Definition low_eq_cone_category (K : Functor J D)
  := ConeCat K.

Context (F : Functor C D) (G : Functor D C) (A : F ⊣ G).
Context (K : Functor J D) (L : @Ob D) (κ : L ⇒Δ K) (Hκ : is_limit κ).
Definition mixed_right_adjoint_limit
  : is_limit (MapCone G κ)
  := right_adjoint_preserves_limit A Hκ.
End LimitLevels.

(** Duality and colimit adjunctions preserve independent target hom/equality
    levels, even when the diagram objects live at a higher level. *)

(** 即使图式对象处于更高层级，对偶与余极限伴随仍保持目标 Hom 及相等层级独立。 *)

Section ColimitLevels.
Universe o h p n l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < l.
Context (J : Cat@{n h p l l}).
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).

Definition high_eq_colimit_adjunction
  : HasColimitsOfShape C J ↔
      ∃ L : Functor (Fct J C) C, L ⊣ Δ[J,C]
  := colimits_iff_diagonal_left_adjoint J C.

Definition low_eq_colimit_adjunction
  : HasColimitsOfShape D J ↔
      ∃ L : Functor (Fct J D) D, L ⊣ Δ[J,D]
  := colimits_iff_diagonal_left_adjoint J D.

Definition high_eq_limit_duality (K : Functor J C) {L}
    (κ : L ⇒Δ K)
  : is_limit κ ↔ is_colimit (ConeOp κ)
  := limit_iff_op_colimit κ.

Definition low_eq_limit_duality (K : Functor J D) {L}
    (κ : L ⇒Δ K)
  : is_limit κ ↔ is_colimit (ConeOp κ)
  := limit_iff_op_colimit κ.

Context (F : Functor C D) (G : Functor D C) (A : F ⊣ G).
Context (K : Functor J C) (L : @Ob C) (κ : K ⇒∇ L).

Definition mixed_left_adjoint_colimit (Hκ : is_colimit κ)
  : is_colimit (MapCocone F κ)
  := left_adjoint_preserves_colimit A Hκ.

End ColimitLevels.

(** Named dual structures and both shape conversions preserve independent
    hom-carrier and equality-witness levels. *)

(** 命名对偶结构及双向形状转换保持 Hom 载体与相等见证层级独立。 *)

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

(** 两种有限余极限基础的双向转换保持 Hom／相等层级独立，兼容两种大小顺序。 *)

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

(** 形状变换可反转形状的 Hom 与相等大小顺序并降低对象层级，目标范畴原生两种 Hom 层级的排列均不改变。 *)

Section ReindexedLimitLevels.
Universe o h p n m l.
Constraint Set < h.
Constraint h < p.
Constraint p < n.
Constraint n < m.
Constraint m < l.
Context (I : Cat@{m p h l l}) (J : Cat@{n h p l l}).
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (Q : Functor I J) (HF : is_full Q) (HQ : is_essentially_surjective Q).
Context (K : Functor J C) (K' : Functor J D).
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

(** 锥比较共享环境上界而不合并两侧形状的原生层级；环境载体与相等的大小顺序也可变化。 *)

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

(** 余极限形状传递的两个方向保留目标独立的 Hom／相等层级。 *)

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

(** 有限覆盖不合并形状与目标范畴的对象、Hom 或相等层级；两种 Hom 与相等大小排列
    均须保持独立。 *)

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
Context `{HGC : !HasFiniteGenerators J} `{HGD : !HasFiniteGenerators K}.
Context `{HTC : !HasTerminal C} `{HTD : !HasTerminal D}.
Context `{HPC : !HasProduct C} `{HPD : !HasProduct D}.
Context `{HEC : !HasEqualizer C} `{HED : !HasEqualizer D}.
Context `{HPbC : !HasPullback C} `{HPbD : !HasPullback D}.

Definition high_eq_finite_hom_generators
  : HasFiniteGenerators J
  := FiniteHomGenerators.
Definition low_eq_finite_hom_generators
  : HasFiniteGenerators K
  := FiniteHomGenerators.
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
Definition high_eq_finite_limit (F : Functor J C)
  : HasLimit C F
  := FiniteLimit F.
Definition low_eq_finite_limit (F : Functor K D)
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

(** 反有限见证与两套基础给出余极限，而不合并形状或目标宇宙。 *)

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

(** 图的边载体与相等层级独立；路径包含中间顶点，其生成相等也包含原边见证。提高载体不得强制提高见证。 *)

Section GraphLevels.
Universe o e p n l.
Constraint o < e.
Constraint e < p.
Constraint p < n.
Constraint n < l.
Context (G : Graph@{o e p}) (H : Graph@{o p e}) (K : Graph@{n e p}).

Definition high_eq_graph_path (x y : @Vertex G)
  : Type@{e}
  := Path G x y.
Definition low_eq_graph_path (x y : @Vertex H)
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
  : Functor (FreeCat G) C
  := FreeF R.
Definition low_eq_free_interpretation
  : Functor (FreeCat G) D
  := FreeF S.

Definition high_eq_finite_graph {n : nat} (k : Fin n → Fin n → nat)
  : Graph@{o e p}
  := FiniteGraph k.
Definition low_eq_finite_graph {n : nat} (k : Fin n → Fin n → nat)
  : Graph@{o p e}
  := FiniteGraph k.

Context `{HEC : !HasEqualizer C} `{HED : !HasEqualizer D}.
Context `{HOC : !HasLimitsOfShape C (DiscreteCat (@Vertex G))}.
Context `{HGC : !HasLimitsOfShape C (DiscreteCat (GraphEdges G))}.
Context `{HOD : !HasLimitsOfShape D (DiscreteCat (@Vertex G))}.
Context `{HGD : !HasLimitsOfShape D (DiscreteCat (GraphEdges G))}.
Definition high_eq_graph_generated_limits
  := @GraphProductsEqualizerLimits G C HOC HGC HEC.
Definition low_eq_graph_generated_limits
  := @GraphProductsEqualizerLimits G D HOD HGD HED.

Context (HFC : ∀ x : @Vertex G,
  HasLimitsOfShape C (DiscreteCat (∃ y : @Vertex G, Edge x y))).
Context (HFD : ∀ x : @Vertex G,
  HasLimitsOfShape D (DiscreteCat (∃ y : @Vertex G, Edge x y))).
Definition high_eq_sigma_edge_products
  := @SigmaProductLimits C (@Vertex G) (λ x, ∃ y : @Vertex G, Edge x y) HOC HFC.
Definition low_eq_sigma_edge_products
  := @SigmaProductLimits D (@Vertex G) (λ x, ∃ y : @Vertex G, Edge x y) HOD HFD.
(** Opposite graph colimits need only vertex and generator-source coproducts,
    while preserving either ordering of target hom and equality levels. *)

(** 反图余极限仅需顶点与生成边源对象余积，并保持目标 Hom 与相等的两种大小顺序。 *)

Context `{HQC : !HasCoequalizer C} `{HQD : !HasCoequalizer D}.
Context `{HCO : !HasColimitsOfShape C (DiscreteCat (@Vertex G))}.
Context `{HCG : !HasColimitsOfShape C (DiscreteCat (GraphEdges (G^opG)))}.
Context `{HDO : !HasColimitsOfShape D (DiscreteCat (@Vertex G))}.
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

(** 形状比较及其对角伴随必须适用于目标范畴原生 Hom 与相等层级的两种排列。 *)

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
  := @LimitAdjunction PairShape C (ProductLimits (C := C)).
Definition low_eq_product_diagonal
  := @LimitAdjunction PairShape D (ProductLimits (C := D)).
Definition high_eq_pullback_diagonal
  := @LimitAdjunction CospanShape C (PullbackLimits (C := C)).
Definition low_eq_pullback_diagonal
  := @LimitAdjunction CospanShape D (PullbackLimits (C := D)).
Definition high_eq_empty_diagonal
  := @LimitAdjunction EmptyShape C (TerminalLimits (C := C)).
Definition low_eq_empty_diagonal
  := @LimitAdjunction EmptyShape D (TerminalLimits (C := D)).
Definition high_eq_equalizer_diagonal
  := @LimitAdjunction ParallelShape C (EqualizerLimits (C := C)).
Definition low_eq_equalizer_diagonal
  := @LimitAdjunction ParallelShape D (EqualizerLimits (C := D)).
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

(** 两个积索引的大小可以超过目标 Hom；一般等化子公式必须保留 Hom 与相等的两种大小排列。 *)

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
Definition high_eq_product_equalizer_limit (K : Functor J C)
  := ProductsEqualizerLimit K.
Definition low_eq_product_equalizer_limit (K : Functor J D)
  := ProductsEqualizerLimit K.
(** The dual constructor needs only its two discrete coproduct choices;
    these large indices do not constrain the target hom/equality order. *)

(** 对偶构造仅需两个离散余积选择；这些大索引不约束目标 Hom／相等的大小顺序。 *)

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

(** 小索引范畴不得等同目标范畴原生 Hom 与相等层级，包括带关系的图式。 *)

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

(** 同一 Hom 范畴必须通过双范畴投影保留独立的一胞、二胞及二胞相等层级。 *)

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

(** 可表性与 Yoneda 同构保留 Hom 与相等的两种排列；同构使用足够大的环境集合范畴。 *)

Section RepresentableLevels.
Universe o h p l.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (F : Functor C SetCat@{h p _ _ _ _ _}).
Context (P : Functor (D^op) SetCat@{p h _ _ _ _ _}).

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

(** 选定拉回实例曾错误合并这两个层级。 *)

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

(** 代码可大于上下文；解码纤维决定两个上下文层级，它们在两种排列下都保持独立。 *)

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

(** 表示不得等同 Hom、项或相等见证层级。 *)

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

(** Raw syntax accepts arbitrary signature levels. An inferred extra universe
    on variable markers must not restrict rename/substitution clients. *)

(** 原始语法允许任意签名层级；变量标记上多余的推断宇宙不得限制重命名或替换的
    使用者。 *)

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

(** βη 见证可严格高于原始语法；打包广集与保相等操作时必须保持该层级。 *)

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

(** 上下文、βη 见证及范畴律允许三个严格递增的层级，选定终对象、积、CCC 及
    上下文打包同构保持这些层级。 *)

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
  : CCC separated_syntactic_category
  := CtxCat_CCC B.
Definition separated_type_syntactic_ccc
  : CCC (TyCat@{b e l} B)
  := TyCat_CCC B.

Definition separated_stlc_completeness (Γ : Ctx B) (A : STLC.Syntax.Ty B)
    (t u : STLC.Syntax.Tm Γ A)
  : TmEq@{b e _} t u ↔ TmModelEq@{b e l _ _ _ _} t u
  := tm_soundness_iff_completeness t u.

Definition separated_stlc_presentations
  : (TyCat@{b e l} B) ≅[CatCat] (CtxCat@{b e l} B)
  := ContextCategoryEquivalence B.
End STLCCategoryLevels.

(** Semantic interpretation preserves separated syntax levels and permits
    either ordering of target hom carriers and equality witnesses. *)

(** 语义解释保持语法层级分离，并允许目标 Hom 载体与相等见证的两种大小排列。 *)

Section STLCInterpretationLevels.
Universes b e l o h p a.
Constraint b < e.
Constraint e < l.
Constraint h < p.
Constraint p < a.
Context (B : Type@{b}) (C : Cat@{o h p a a})
    (D : Cat@{o p h a a}) (HC : CCC C) (HD : CCC D).
Local Existing Instance HC.
Local Existing Instance HD.
Context (I : B → @Ob C) (J : B → @Ob D).

Definition high_eq_stlc_interpretation
  : Functor (CtxCat@{b e l} B) C
  := InterpretF I.
Definition low_eq_stlc_interpretation
  : Functor (CtxCat@{b e l} B) D
  := InterpretF J.

Context (F : Functor (TyCat@{b e l} B) C)
    (HF : IsCCCF F (TyCat_CCC B) HC).
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

(** 群胚取逆、反范畴、积与函子范畴保持 Hom 载体与相等见证的两种大小排列。 *)

Section GroupoidLevels.
Universes o h p l.
Constraint h < p.
Constraint p < l.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l})
    (HC : IsGroupoid C) (HD : IsGroupoid D).
Local Existing Instance HC.
Local Existing Instance HD.

Definition high_eq_groupoid_inverse {X Y : @Ob C} (f : Hom X Y)
  : Hom Y X
  := f⁻¹.

Definition low_eq_groupoid_inverse_functor
  : Functor (D^op) D
  := InvF D.

Definition high_eq_opposite_groupoid
  : C^op ⦂ Gpd
  := op_IsGroupoid C.

Definition mixed_groupoid_product
  : (C ×C D) ⦂ Gpd
  := ProdCat_IsGroupoid C D.

Definition low_eq_functor_groupoid
  : Fct C D ⦂ Gpd
  := Fct_IsGroupoid C D.
End GroupoidLevels.

(** Setoid elements and their equality witnesses remain independent in the
    equality groupoid; its equality between parallel arrows is small. *)

(** 相等群胚保持广集元素与其相等见证的大小独立，平行箭头间的相等使用小类型。 *)

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
  := EqGpd_IsGroupoid X.
End EqualityGroupoidLevels.

(** Delooping and the regular action preserve independent carrier and
    equality-witness sizes, in both orders. Law bounds are auxiliary. *)

(** 单对象群胚与正则作用保持载体与相等见证两种次序下的大小独立，定律上界
    使用辅助宇宙。 *)

Section GroupDeloopingLevels.
Universes u p l.
Constraint u < p.
Constraint p < l.
Context (X : SetC@{u p}) (Y : SetC@{p u})
    (GX : Group@{u p l} X) (GY : Group@{p u l} Y).
Local Existing Instance GX.
Local Existing Instance GY.

Definition high_eq_group_category
  : Cat@{Set u p l l}
  := B(X).

Definition low_eq_group_category
  : Cat@{Set p u l l}
  := B(Y).

Definition high_eq_group_category_structure
  : high_eq_group_category ⦂ Gpd
  := MonoidCat_IsGroupoid X.

Definition low_eq_group_category_structure
  : low_eq_group_category ⦂ Gpd
  := MonoidCat_IsGroupoid Y.

Definition high_eq_regular_action
  : Functor high_eq_group_category SetCat@{u p _ _ _ _ _}
  := RegularActionF X.

Definition low_eq_regular_action
  : Functor low_eq_group_category SetCat@{p u _ _ _ _ _}
  := RegularActionF Y.

Definition high_eq_endomorphism_group
  : Group X
  := EndGroup (HC := high_eq_group_category_structure)
      high_eq_group_category tt.

Definition low_eq_endomorphism_group
  : Group Y
  := EndGroup (HC := low_eq_group_category_structure)
      low_eq_group_category tt.
End GroupDeloopingLevels.

(** Family-action equivalence allows base carrier and equality levels above
    both fiber levels, in either ordering. Auxiliary law bounds remain large. *)

(** 族与作用的等价允许基底载体及相等层级高于两个纤维层级，并允许各自大小
    次序互换；定律上界保持在更大的辅助宇宙中。 *)

Section FamilyActionLevels.
Universes u p b e l.
Constraint u < p.
Constraint p < b.
Constraint b < e.
Constraint e < l.
Context (X : SetC@{b e}) (Y : SetC@{e b}).

Definition high_eq_family_action_equivalence
  : FamSCat X ≃C Fct (EqGpd X) SetCat@{u p _ l _ _ _}
  := fam_action_equiv X.

Definition low_eq_family_action_equivalence
  : FamSCat X ≃C Fct (EqGpd X) SetCat@{p u _ l _ _ _}
  := fam_action_equiv X.

Definition reversed_base_family_action_equivalence
  : FamSCat Y ≃C Fct (EqGpd Y) SetCat@{u p _ l _ _ _}
  := fam_action_equiv Y.

Definition reversed_base_low_eq_family_action_equivalence
  : FamSCat Y ≃C Fct (EqGpd Y) SetCat@{p u _ l _ _ _}
  := fam_action_equiv Y.
End FamilyActionLevels.

(** The action-slice specialization retains the family-slice size bound,
    while admitting a strictly smaller base-equality universe. *)

(** 作用与切片的特化保留族与切片的大小条件，并允许基底相等宇宙严格较小。 *)

Section ActionSliceLevels.
Universes u p.
Constraint p < u.
Context (X : SetC@{u p}).

Definition distinct_action_slice_equivalence
  : Fct (EqGpd X) SetCat@{u p _ _ _ _ _} ≃C
      (SetCat@{u p _ _ _ _ _} /C X)
  := action_slice_equiv X.
End ActionSliceLevels.

(** Interpreting finite ordinals in the category of categories does not raise
    the simplex category's object, arrow, equality or law universes. *)

(** 在范畴之范畴中解释有限序数，不提升单纯范畴的对象、箭头、相等或定律宇宙。 *)

Definition small_simplex_category
  : Cat@{Set Set Set Set Set}
  := SimplexCat.

(** Standard simplices and their Yoneda correspondence admit either ordering
    of the carrier and equality levels of the simplicial set's values. *)

(** 标准单形及其 Yoneda 对应允许单纯集合值的载体与相等层级采用任一大小次序。 *)

Section SimplicialLevels.
Universes u p.
Constraint u < p.
Context (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _})
    (Y : Functor (Δ^op) SetCat@{p u _ _ _ _ _}).

Definition high_eq_standard_simplex (n : nat)
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Δ[n].

Definition low_eq_standard_simplex (n : nat)
  : Functor (Δ^op) SetCat@{p u _ _ _ _ _}
  := Δ[n].

Definition high_eq_simplex_yoneda (n : nat)
  : LiftS (Nat_SetS Δ[n] X) ≅[SetCat] LiftS (X n)
  := simplex_element_iso n.

Definition low_eq_simplex_yoneda (n : nat)
  : LiftS (Nat_SetS Δ[n] Y) ≅[SetCat] LiftS (Y n)
  := simplex_element_iso n.

(** Standard-simplex comparisons retain both orderings after passing through
    the general category-probe construction. *)

(** 标准单形比较经过一般范畴探测构造后，仍保留两种大小次序。 *)

Definition high_eq_standard_nerve (n : nat)
  : (Δ[n] : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N N≅([Ord n])
  := standard_nerve_iso n.

Definition low_eq_standard_nerve (n : nat)
  : (Δ[n] : Functor (Δ^op) SetCat@{p u _ _ _ _ _}) ≅N N≅([Ord n])
  := standard_nerve_iso n.
End SimplicialLevels.

(** Small ordinal probes accept larger categories with independent object,
    arrow and equality sizes. Value equality need not dominate object size,
    and can also be raised above the value carrier. *)

(** 小序数探测接受对象、箭头及相等大小独立的较大范畴；值相等不必高于对象大小，
    也可以提升到值载体之上。 *)

Section NerveLevels.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.
Context (C : Cat@{o h e l l}) (D : Cat@{e h o l l}).

Definition low_eq_large_diagram_nerve
  : Functor (Δ^op) SetCat@{u h _ _ _ _ _}
  := N≅(C).

Definition high_eq_large_diagram_nerve
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := N≅(D).
End NerveLevels.

(** Native monoid nerves retain either ordering of carrier and equality
    levels. Their diagram comparisons raise both sides explicitly, with
    either ordering also permitted at the common ambient sizes. *)

(** 原生幺半群 nerve 保留载体与相等层级的两种次序；图式比较显式提升两侧，
    共同环境大小也允许两种次序。 *)

Section MonoidNerveLevels.
Universes u p c e.
Constraint u < p.
Constraint p < c.
Constraint c < e.
Context (M : SetC@{u p}) (N : SetC@{p u})
    `{HM : !Monoid M} `{HN : !Monoid N}.

Definition high_eq_monoid_nerve
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Nₘ(M).

Definition low_eq_monoid_nerve
  : Functor (Δ^op) SetCat@{p u _ _ _ _ _}
  := Nₘ(N).

Definition high_eq_monoid_comparison
  : (LiftF ∘F Nₘ(M) : Functor (Δ^op) SetCat@{c e _ _ _ _ _}) ⇒ N≅(B(M))
  := MonoidDiagramN.

Definition low_eq_monoid_comparison
  : (LiftF ∘F Nₘ(N) : Functor (Δ^op) SetCat@{e c _ _ _ _ _}) ⇒ N≅(B(N))
  := MonoidDiagramN.
End MonoidNerveLevels.
