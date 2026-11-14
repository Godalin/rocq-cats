From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Arrow.Core
  Cat.Limit.Core
  Cat.Limit.Transport
  Cat.Colimit.Core
  Cat.Colimit.Construction
  Cat.Colimit.Graph.Core
  Cat.Colimit.Graph.Finite
  Cat.Colimit.Finite
  Instance.Set.Core
  Instance.Set.Initial
  Instance.Set.Coproduct
  Instance.Set.Coequalizer.
From Cats.Set Require Export
  IndexedSum.

(** * Colimits in the Category of Setoids *)

(** * 广集范畴中的余极限 *)

(** An indexed disjoint sum has the original opposite discrete-limit
    property. Generated equality supplies respectfulness without UIP. *)

(** 指标不交和具有原反离散极限性质；生成相等无需 UIP 即给出保相等性。 *)

Program Definition SetCat_IndexedCoproductColimit@{i u p +} {I : Type@{i}}
    (D : Fct (DiscreteCat I) (SetCat@{u p _ _ _ _ _}))
  : HasColimit SetCat D
  :=
  {|hasOpLimit :=
      {|Lim := ∐S[λ i, D i]
      ; limit_cone := op_cone (@DiscreteCocone SetCat I D _
          (indexed_sum_inj_resp (λ i, D i)))
      |}
  |}.
Next Obligation.
  intros X μ. exists (indexed_sum_case_resp (λ i, μ i)).
  refine {|this := _
         ; that := _
         |}.
  - intros i x. reflexivity.
  - intros h H [i x]. exact (H i x).
Defined.

(** Explicitly enable all coproducts over the given index type. The model
    requires [i ≤ u ≤ p]; no resizing is used. *)

(** 显式启用给定索引类型上的全部余积；模型要求 [i ≤ u ≤ p]，不使用大小重设。 *)

Program Definition SetCat_HasIndexedCoproducts@{i u p +} (I : Type@{i})
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) (DiscreteCat I)
  :=
  {|hasOpLimits :=
      {|hasLimit D := @TransportedLimit _ (SetCat^op) _ D
          (OpUnopF D).1 (OpUnopF D).2
          (@hasOpLimit SetCat _ _
            (SetCat_IndexedCoproductColimit (D^unopF)))
      |}
  |}.

(** Finite coproducts use initial objects and binary sums, so unlike the
    general generated indexed-sum model they need no bound [u ≤ p]. *)

(** 有限余积使用始对象及二元和，因此不同于一般生成指标和模型，不需要 [u ≤ p]。 *)

Definition SetCat_FiniteCoproductColimits@{u p +} (n : nat)
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) (DiscreteCat (Fin n))
  := @FiniteCoproductColimits SetCat SetCat_HasInitial SetCat_HasCoproduct n.

(** Nested indexed coproducts instantiate the dependent-index theorem with
    the same explicit model size bounds. *)

(** 嵌套指标余积以同样显式的模型大小界实例化依赖索引定理。 *)

Definition SetCat_SigmaCoproductColimits@{u p +} {I : Type} (J : I → Type)
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) (DiscreteCat (∃ i, J i))
  := @SigmaCoproductColimits SetCat I J (SetCat_HasIndexedCoproducts I)
      (λ i, SetCat_HasIndexedCoproducts (J i)).

(** Two particular coproducts and the chosen coequalizers give a general
    diagram colimit through the shared abstract constructor. *)

(** 两个特定余积及选定余等化子通过共用抽象构造给出一般图式余极限。 *)

Definition SetCat_DiagramColimit@{u p +} {J : Cat}
    (D : Fct J (SetCat@{u p _ _ _ _ _}))
  : HasColimit SetCat D
  := @CoproductsCoequalizerColimit J SetCat D
      (SetCat_IndexedCoproductColimit (DiscreteF (CodiagramObj D)))
      (SetCat_IndexedCoproductColimit (DiscreteF (CodiagramSources D)))
      SetCat_HasCoequalizer.

(** Select all colimits of a size-bounded shape by the original opposite
    product/equalizer theorem. *)

(** 通过原反积／等化子定理选择大小有界形状的全部余极限。 *)

Definition SetCat_HasColimitsOfShape@{u p +} (J : Cat)
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) J
  := @IndexedCoproductsCoequalizerColimits J SetCat
      (SetCat_HasIndexedCoproducts (@Ob J))
      (SetCat_HasIndexedCoproducts (ArrowOb (J^op))) SetCat_HasCoequalizer.

(** Graph-generated colimits use coproducts over vertices and reversed
    generators rather than all paths. *)

(** 图生成余极限使用顶点及反向生成边上的余积，而不按全部路径取余积。 *)

Definition SetCat_GraphColimits@{u p +} (G : Graph)
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) (FreeCat G)
  := @GraphCoproductsCoequalizerColimits G SetCat
      (SetCat_HasIndexedCoproducts (@Vertex G))
      (SetCat_HasIndexedCoproducts (GraphEdges (G^opG)))
      SetCat_HasCoequalizer.

(** Finite colimits reuse initial objects, binary coproducts and coequalizers;
    finite covers avoid a bound on the shape's raw object and arrow types. *)

(** 有限余极限复用始对象、二元余积及余等化子；有限覆盖避免约束形状原始对象及
    箭头类型的大小。 *)

Definition SetCat_FiniteColimits@{u p +} {J : Cat}
    `{HJ : !HasFiniteHomCover J}
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) J
  := @FiniteColimits SetCat J SetCat_HasInitial SetCat_HasCoproduct
      SetCat_HasCoequalizer HJ.

(** Finite generators give colimits even when cycles generate infinitely
    many paths or the target shape imposes additional equations. *)

(** 即使环生成无限多条路径或目标形状施加额外方程，有限生成元仍给出余极限。 *)

Definition SetCat_GeneratedColimits@{u p +} {J : Cat}
    `{HJ : !HasFiniteGen J}
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) J
  := @GeneratedColimits SetCat J SetCat_HasInitial SetCat_HasCoproduct
      SetCat_HasCoequalizer HJ.

(** Specialize the same chosen structures to finite free graphs. *)

(** 将同一选定结构特化到有限自由图。 *)

Definition SetCat_FiniteGraphColimits@{u p +} {n : nat}
    (k : Fin n → Fin n → nat)
  : HasColimitsOfShape (SetCat@{u p _ _ _ _ _}) (FreeCat (FiniteGraph k))
  := @FiniteGraphColimits SetCat SetCat_HasInitial SetCat_HasCoproduct
      SetCat_HasCoequalizer n k.
