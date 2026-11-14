From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Arrow.Core
  Cat.Limit.Core
  Cat.Limit.Construction
  Cat.Limit.Graph.Core
  Cat.Limit.Graph.Finite
  Cat.Limit.Finite
  Cat.Product.Sigma
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Equalizer.
From Cats.Set Require Export
  Pi.

(** * Limits in the Category of Setoids *)

(** * 广集范畴中的极限 *)

(** Dependent functions give a discrete limit with pointwise equality.
    The index universe must fit both carrier and equality universes. *)

(** 依赖函数按逐点相等给出离散极限；索引宇宙须同时容纳于载体及相等宇宙。 *)

Program Definition SetCat_IndexedProductLimit@{i u p +} {I : Type@{i}}
    (D : Fct (DiscreteCat I) (SetCat@{u p _ _ _ _ _}))
  : HasLimit SetCat D
  :=
  {|Lim := ∏S[λ i, D i]
  ; limit_cone := @DiscreteCone SetCat I D _ (pi_proj_resp (λ i, D i))
  |}.
Next Obligation.
  intros X μ. exists (pi_pair_resp (λ i, μ i)).
  refine {|this := _
         ; that := _
         |}.
  - intros i x. reflexivity.
  - intros h H x i. exact (H i x).
Defined.

(** Explicitly enable all products indexed by the given discrete type. *)

(** 显式启用由给定离散类型索引的全部积。 *)

Program Definition SetCat_HasIndexedProducts@{i u p +} (I : Type@{i})
  : HasLimitsOfShape (SetCat@{u p _ _ _ _ _}) (DiscreteCat I)
  :=
  {|hasLimit := SetCat_IndexedProductLimit
  |}.

(** Finite products also follow from the binary model, with no comparison
    between carrier and equality universes. *)

(** 有限积也由二元模型得到，不要求比较载体与相等宇宙。 *)

Definition SetCat_FiniteProductLimits@{u p +} (n : nat)
  : HasLimitsOfShape (SetCat@{u p _ _ _ _ _}) (DiscreteCat (Fin n))
  := @FiniteProductLimits SetCat SetCat_HasTerminal SetCat_HasProduct n.

(** Nested indexed products instantiate the general dependent-index theorem. *)

(** 嵌套指标积实例化一般依赖索引定理。 *)

Definition SetCat_SigmaProductLimits@{u p +} {I : Type} (J : I → Type)
  : HasLimitsOfShape (SetCat@{u p _ _ _ _ _}) (DiscreteCat (∃ i, J i))
  := @SigmaProductLimits SetCat I J (SetCat_HasIndexedProducts I)
      (λ i, SetCat_HasIndexedProducts (J i)).

(** Reuse object/arrow indexed products and the chosen equalizer to construct
    one general diagram limit. Inferred size bounds remain on the shape. *)

(** 复用对象／箭头指标积及选定等化子构造单个一般图式极限；大小界保留于形状。 *)

Definition SetCat_DiagramLimit@{u p +} {J : Cat}
    (D : Fct J (SetCat@{u p _ _ _ _ _}))
  : HasLimit SetCat D
  := @ProductsEqualizerLimit J SetCat D
      (@hasLimit SetCat _ (SetCat_HasIndexedProducts (@Ob J)) _)
      (@hasLimit SetCat _ (SetCat_HasIndexedProducts (ArrowOb J)) _)
      SetCat_HasEqualizer.

(** Select all limits of a shape within the model's inferred size bounds. *)

(** 在模型推导出的大小界内选择一个形状的全部极限。 *)

Definition SetCat_HasLimitsOfShape@{u p +} (J : Cat)
  : HasLimitsOfShape (SetCat@{u p _ _ _ _ _}) J
  := @IndexedProductsEqualizerLimits J SetCat
      (SetCat_HasIndexedProducts (@Ob J))
      (SetCat_HasIndexedProducts (ArrowOb J)) SetCat_HasEqualizer.

(** For free shapes, only vertex and generator products are required. *)

(** 对自由形状，只要求顶点及生成边积。 *)

Definition SetCat_GraphLimits@{u p +} (G : Graph)
  : HasLimitsOfShape (SetCat@{u p _ _ _ _ _}) (FreeCat G)
  := @GraphProductsEqualizerLimits G SetCat
      (SetCat_HasIndexedProducts (@Vertex G))
      (SetCat_HasIndexedProducts (GraphEdges G)) SetCat_HasEqualizer.

(** Finite-shape limits reuse the already selected terminal, product and
    equalizer models; they do not bound the shape by its raw object size. *)

(** 有限形状极限复用已选定终对象、积及等化子模型，不按形状原始对象大小施加界。 *)

Definition SetCat_FiniteLimits@{u p +} {J : Cat}
    `{HJ : !HasFiniteHomCover J}
  : HasLimitsOfShape (SetCat@{u p _ _ _ _ _}) J
  := @FiniteLimits SetCat SetCat_HasTerminal SetCat_HasProduct
      SetCat_HasEqualizer J HJ.

(** Finite generators also suffice when the shape has infinitely many paths. *)

(** 即使形状具有无限多条路径，有限生成元也已经足够。 *)

Definition SetCat_GeneratedLimits@{u p +} {J : Cat}
    `{HJ : !HasFiniteGen J}
  : HasLimitsOfShape (SetCat@{u p _ _ _ _ _}) J
  := @GeneratedLimits SetCat SetCat_HasTerminal SetCat_HasProduct
      SetCat_HasEqualizer J HJ.

(** The finite-free-graph specialization keeps the original construction. *)

(** 有限自由图特化保留原构造。 *)

Definition SetCat_FiniteGraphLimits@{u p +} {n : nat}
    (k : Fin n → Fin n → nat)
  : HasLimitsOfShape (SetCat@{u p _ _ _ _ _}) (FreeCat (FiniteGraph k))
  := @FiniteGraphLimits SetCat SetCat_HasTerminal SetCat_HasProduct
      SetCat_HasEqualizer n k.
