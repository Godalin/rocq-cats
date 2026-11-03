From Cats Require Import STLC.Product.
From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Bicategory
  Cat.Bicategory.Thin.
From Cats Require Import Cat.CCC.
From Cats Require Import
  Cat.Product
  Cat.Exponential
  Cat.Exponential.Functor
  Instance.Set.ExponentialHom.
From Cats Require Import
  Cat.Adjunction
  Instance.Set.Adjunction.
From Cats Require Import
  Cat.Diagram
  Cat.Limit
  Cat.Limit.Adjunction
  Cat.Limit.Preservation.
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
  Cat.Limit.Reindex.
From Cats Require Import
  DTT.CwF
  DTT.Context.Extension
  DTT.Context.Conversion.
From Cats Require Import DTT.Context.Representation.
From Cats Require Import
  DTT.Display
  DTT.Context.Display.
From Cats Require Import DTT.Display.Section.
From Cats Require Import DTT.Context.Pullback.
From Cats Require Import DTT.Comprehension.
From Cats Require Import
  Cat.Arrow
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
    increasing levels. Chosen terminal and product structures preserve them. *)

(** 上下文、βη 见证及范畴律允许三个严格递增的层级，选定终对象与积保持这些
    层级。 *)

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
End STLCCategoryLevels.
