From Cats Require Export
  Instance.Set.Simplicial.Standard
  Cat.Homotopy.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core
  Cat.Functor.FiniteProducts
  Instance.Set.Product
  Instance.Set.Terminal.

Local Open Scope nat_scope.

(** * Elementary Simplicial Homotopy

    The time interval is the standard simplex [Δ[1]]. In degree n, time
    is a monotone map [n] to [1], and restriction acts on the simplex and
    time together. A homotopy [X × Δ[1] ⇒ Y] retains its full simplicial
    map and its two endpoint equations. This elementary directed relation
    is not assumed symmetric or transitive for arbitrary simplicial setoids. *)

(** * 初等单纯同伦

    时间区间为标准单形 [Δ[1]]。在 n 维中，时间是从 [n] 到 [1] 的保序映射；
    限制同时作用于单形和时间。同伦 [X × Δ[1] ⇒ Y] 保留完整单纯映射及其两个
    端点方程。对任意单纯广集，不假设此初等有向关系具有对称性或传递性。 *)

(** The two finite positions choose the interval's initial and final vertex. *)

(** 两个有限位置选取区间的起始及终止顶点。 *)

Definition simplex_interval_position (b : bool)
  : Ordinal 1
  := if b then fin_next fin_first else fin_first.

Section SimplicialHomotopies.
Universes u r.

Let simplicial_terminal
  : HasTerminal (Fct (Δ^op) SetCat@{u r _ _ _ _ _})
  := @Fct_HasTerminal _ _ SetCat_HasTerminal.

Let simplicial_product
  : HasProduct (Fct (Δ^op) SetCat@{u r _ _ _ _ _})
  := @Fct_HasProduct _ _ SetCat_HasProduct.

Local Existing Instance simplicial_terminal.
Local Existing Instance simplicial_product.

(** A constant ordinal map supplies each endpoint in every dimension. *)

(** 常值序数映射在每个维度给出相应端点。 *)

Program Definition SimplicialIntervalPointN (b : bool)
  : ConstF (Δ^op) (C := SetCat@{u r _ _ _ _ _}) UnitS@{u r} ⇒ Δ[1]
  :=
  {|nt n :=
      {|func x :=
          {|lower := ConstF [Ord n] (C := [Ord 1])
              (simplex_interval_position b)
          |}
      |}
  |}.
Next Obligation.
  intros x y H. refine {|lower := _
                       |}. reflexivity.
Defined.
Next Obligation.
  intros x. refine {|lower := _
                    |}.
  apply (snd (simplex_eq_iff _ _)). intros i. reflexivity.
Defined.

(** The interval uses explicitly supplied pointwise finite products;
    importing this module does not register chosen model structures. *)

(** 区间使用显式提供的点态有限积；导入此模块不注册选定模型结构。 *)

Program Definition SimplicialInterval
  : Interval (Fct (Δ^op) SetCat@{u r _ _ _ _ _})
  :=
  {|interval_object := Δ[1]
  ; interval_point := SimplicialIntervalPointN
  |}.

(** The cylinder is the pointwise product with the standard interval. *)

(** 柱为与标准区间的点态积。 *)

Definition SimplicialCylinderF
  : Functor (Fct (Δ^op) SetCat@{u r _ _ _ _ _})
      (Fct (Δ^op) SetCat@{u r _ _ _ _ _})
  := CylinderF SimplicialInterval.

(** The endpoint inclusion is natural in the source simplicial setoid. *)

(** 端点嵌入在源单纯广集上自然。 *)

Definition SimplicialEndpointN
    (X : Functor (Δ^op) SetCat@{u r _ _ _ _ _}) (b : bool)
  : X ⇒ SimplicialCylinderF X
  := CylinderEndpointN SimplicialInterval b X.

(** A simplicial homotopy is the generic interval homotopy specialized
    to pointwise products and [Δ[1]], with the same transparent witness. *)

(** 单纯同伦将通用区间同伦特化至点态积和 [Δ[1]]，保留相同透明见证。 *)

Definition SimplicialHomotopy
    {X Y : Functor (Δ^op) SetCat@{u r _ _ _ _ _}} (f g : X ⇒ Y)
  : Type
  := Homotopy SimplicialInterval f g.

(** The first restriction recovers the initial map in natural equality. *)

(** 第一个限制在自然相等下恢复起始映射。 *)

Lemma simplicial_homotopy_0
    {X Y : Functor (Δ^op) SetCat@{u r _ _ _ _ _}} {f g : X ⇒ Y}
    (H : SimplicialHomotopy f g)
  : (homotopy_map H ∘Nv SimplicialEndpointN X false) ≈N f.
Proof. exact (homotopy_endpoint H false). Defined.

(** The second restriction recovers the final map. *)

(** 第二个限制恢复终止映射。 *)

Lemma simplicial_homotopy_1
    {X Y : Functor (Δ^op) SetCat@{u r _ _ _ _ _}} {f g : X ⇒ Y}
    (H : SimplicialHomotopy f g)
  : (homotopy_map H ∘Nv SimplicialEndpointN X true) ≈N g.
Proof. exact (homotopy_endpoint H true). Defined.

(** Every simplicial map has a constant homotopy. *)

(** 每个单纯映射都有恒定同伦。 *)

Definition SimplicialConstantHomotopy
    {X Y : Functor (Δ^op) SetCat@{u r _ _ _ _ _}} (f : X ⇒ Y)
  : SimplicialHomotopy f f
  := ConstantHomotopy SimplicialInterval f.

(** Precomposition restricts a homotopy along a simplicial map. *)

(** 预复合沿单纯映射限制同伦。 *)

Definition SimplicialPreHomotopy
    {W X Y : Functor (Δ^op) SetCat@{u r _ _ _ _ _}}
    {f g : X ⇒ Y} (H : SimplicialHomotopy f g) (a : W ⇒ X)
  : SimplicialHomotopy (f ∘Nv a) (g ∘Nv a)
  := @PreHomotopy _ simplicial_terminal simplicial_product
      SimplicialInterval W X Y f g H a.

(** Postcomposition applies a simplicial map to a homotopy. *)

(** 后复合将单纯映射作用于同伦。 *)

Definition SimplicialPostHomotopy
    {X Y Z : Functor (Δ^op) SetCat@{u r _ _ _ _ _}}
    {f g : X ⇒ Y} (a : Y ⇒ Z) (H : SimplicialHomotopy f g)
  : SimplicialHomotopy (a ∘Nv f) (a ∘Nv g)
  := @PostHomotopy _ simplicial_terminal simplicial_product
      SimplicialInterval X Y Z f g a H.

(** Horizontal composition uses the same time simplex in both factors. *)

(** 水平复合在两个因子中使用同一个时间单形。 *)

Definition SimplicialCompHomotopy
    {X Y Z : Functor (Δ^op) SetCat@{u r _ _ _ _ _}}
    {f g : X ⇒ Y} {a b : Y ⇒ Z}
    (K : SimplicialHomotopy a b) (H : SimplicialHomotopy f g)
  : SimplicialHomotopy (a ∘Nv f) (b ∘Nv g)
  := @CompHomotopy _ simplicial_terminal simplicial_product
      SimplicialInterval X Y Z f g a b K H.

(** The constant endpoint map from any source factors through its terminal
    map, using specified natural equality. *)

(** 来自任意源的常值端点映射通过其终映射分解，使用指定自然相等。 *)

Definition SimplicialConstantPointN
    (X : Functor (Δ^op) SetCat@{u r _ _ _ _ _}) (b : bool)
  : X ⇒ Δ[1]
  := SimplicialIntervalPointN b ∘Nv (@term _ simplicial_terminal X).

(** The interval coordinate supplies a homotopy between its distinct
    constant endpoints; it does not identify them by setoid equality. *)

(** 区间坐标给出其不同常值端点之间的同伦，并不以广集相等识别它们。 *)

Definition SimplicialIntervalHomotopy
    (X : Functor (Δ^op) SetCat@{u r _ _ _ _ _})
  : SimplicialHomotopy (SimplicialConstantPointN X false)
      (SimplicialConstantPointN X true)
  := IntervalHomotopy SimplicialInterval X.

(** In particular the two point maps themselves have an actual homotopy. *)

(** 特别地，两个点映射本身具有实际同伦。 *)

Definition SimplicialPointHomotopy
  : SimplicialHomotopy (SimplicialIntervalPointN false)
      (SimplicialIntervalPointN true).
Proof.
  refine (HomotopyChangeEndpoints
    (SimplicialIntervalHomotopy
      (ConstF (Δ^op) (C := SetCat@{u r _ _ _ _ _}) UnitS@{u r})) _ _);
    intros n x; refine {|lower := _
                        |}; reflexivity.
Defined.

(** The two endpoints are already distinct in degree zero. *)

(** 两个端点在零维就已不同。 *)

Lemma simplicial_interval_endpoints_distinct
  : ¬ (SimplicialIntervalPointN false 0 tt ≈S
      SimplicialIntervalPointN true 0 tt).
Proof.
  intros [H].
  pose proof (fst (simplex_eq_iff _ _) H fin_first) as E.
  pose proof (f_equal fin_rank E) as R. discriminate R.
Defined.

(** Homotopy of the point maps does not make them naturally equal. *)

(** 点映射的同伦并不使它们自然相等。 *)

Lemma simplicial_interval_points_not_equal
  : ¬ (SimplicialIntervalPointN false ≈N SimplicialIntervalPointN true).
Proof.
  intros H. exact (simplicial_interval_endpoints_distinct (H 0 tt)).
Defined.

End SimplicialHomotopies.

Notation "f '∼Δ' g" := (SimplicialHomotopy f g)
  (at level 70, no associativity) : type_scope.
