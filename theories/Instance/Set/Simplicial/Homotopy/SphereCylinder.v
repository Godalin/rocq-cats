From Cats Require Export
  Instance.Set.Simplicial.Homotopy.Core
  Instance.Set.Simplicial.Homotopy.Sphere
  Instance.Set.Simplicial.Boundary.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Diagram.Core.
From Stdlib Require Import
  Lia.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Sphere Homotopies Relative to the Whole Boundary

    A triangle represents a map from [Δ[2]], by
    %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex map resp}
    {%[simplex_map_resp]%}%. A homotopy of two such maps has a whole
    triangle cylinder as its domain. To describe a based sphere homotopy,
    its restriction to [∂Δ[2] × Δ[1]] must stay constant at the base vertex
    throughout time, in every degree. Merely fixing its endpoint triangles
    or its three vertex paths would not impose this relative condition.

    We retain the existing simplicial homotopy and this boundary law.
    Neither Kan filling nor an equivalence-relation law is assumed here. *)

(** * 相对于整个边界的球面同伦

    由 %\coqref{Cats.Instance.Set.Simplicial.Standard.simplex map resp}
    {%[simplex_map_resp]%}%，三角形表示从 [Δ[2]] 出发的映射。两个此类
    映射的同伦以整个三角柱为定义域。要描述基点球面同伦，其沿
    [∂Δ[2] × Δ[1]] 的限制须在每一维、整个时间中恒等于基点的常值单形。
    仅固定端点三角形或三条顶点路径，并不施加这个相对条件。

    这里保留既有单纯同伦及此边界定律，不预设 Kan 填充或等价关系定律。 *)

(** In the square, the lower map represents the base vertex and the left
    map collapses both coordinates to that vertex shape. Commutativity
    means the componentwise specified equalities in
    [is_two_sphere_cylinder_relative], not equality of functions. *)

(** 方图下方映射表示基点顶点，左侧映射将两个坐标压到该顶点形状。交换性指
    [is_two_sphere_cylinder_relative] 中逐分量的指定相等，而非函数相等。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=huge,row sep=large]
\partial\Delta[2]\times\Delta[1] \arrow[r,hook,"{\iota_\partial\times1}"]
  \arrow[d] & \Delta[2]\times\Delta[1] \arrow[d,"H"] \\
\Delta[0] \arrow[r,"{\langle b\rangle}"'] & X
\end{tikzcd}
\end{center}%
*)

(** ** A Relative Cylinder and Its Evaluation

    Fix a simplicial setoid with independent carrier/equality sizes and
    a base vertex. Boundary membership retains a chosen coface factor;
    equality of boundary data ignores that witness. *)

(** ** 相对柱及其求值

    固定载体／相等大小独立的单纯广集及一个基点。边界隶属保留选定余面因子，
    边界数据的相等不比较该见证。 *)

Section SphereCylinders.
Universes u p.
Context (X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).

Let D
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  := Δ[2].

(** The full cylinder map is constant on the actual boundary subpresheaf
    at every time simplex, including all degenerate ones. *)

(** 完整柱映射在实际边界子预层上对每个时间单形均为常值，包括全部退化单形。 *)

Definition is_two_sphere_cylinder_relative (K : SimplicialCylinderF D ⇒ X)
  : Type
  := ∀ n (a : (∂Δ[2] : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
      (t : (Δ[1] : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n),
      K n (ι∂[2] n a, t) ≈S simplex_constant X b n.

(** Retain an actual homotopy between the two represented triangle maps,
    together with its relative boundary equation. *)

(** 保留两个三角形所表示映射之间的实际同伦，以及其相对边界方程。 *)

Definition TwoSphereCylinderHomotopy (x y : TwoSphereS X b)
  : Type
  := ∃ H : SimplicialHomotopy ⟦x.1⟧Δ[X; 2] ⟦y.1⟧Δ[X; 2],
      is_two_sphere_cylinder_relative (homotopy_map H).

(** Endpoint changes retain exactly the same cylinder map. *)

(** 端点替换保留完全相同的柱映射。 *)

Definition TwoSphereCylinderChangeEndpoints
    {x y x' y' : TwoSphereS X b}
    (H : TwoSphereCylinderHomotopy x y) (E : x ≈S x') (F : y ≈S y')
  : TwoSphereCylinderHomotopy x' y'.
Proof.
  exists (HomotopyChangeEndpoints H.1
    (@func_proper _ _ (@simplex_map_resp X 2) _ _ E)
    (@func_proper _ _ (@simplex_map_resp X 2) _ _ F)).
  exact H.2.
Defined.

(** Relative cylinders respect the original sphere equality at both ends. *)

(** 相对柱在两端保持原球面相等。 *)

Global Instance TwoSphereCylinderHomotopy_proper
  : Proper ([≈S] ==> [≈S] ==> iffT) TwoSphereCylinderHomotopy.
Proof.
  intros x x' E y y' F. split; intros H.
  - exact (TwoSphereCylinderChangeEndpoints H E F).
  - exact (TwoSphereCylinderChangeEndpoints H (symmetry E) (symmetry F)).
Defined.

(** Native sphere equality supplies a time-independent relative cylinder.
    The factor retained by each boundary simplex reduces its restriction
    to one of the three constant edges. *)

(** 原生球面相等给出与时间无关的相对柱。每个边界单形保留的分解，将其限制
    归结到三条常值边之一。 *)

Definition TwoSphereConstantCylinder (x y : TwoSphereS X b) (E : x ≈S y)
  : TwoSphereCylinderHomotopy x y.
Proof.
  exists (HomotopyChangeEndpoints
    (SimplicialConstantHomotopy ⟦x.1⟧Δ[X; 2])
    (reflexivity ⟦x.1⟧Δ[X; 2])
    (@func_proper _ _ (@simplex_map_resp X 2) _ _ E)).
  intros n a t.
  destruct a as [[θ [i [f Hf]]]].
  change (X[θ]Δ x.1 ≈S simplex_constant X b n).
  transitivity (X[δ[1; i] ∘ f]Δ x.1).
  - apply simplex_restrict_proper. exact Hf.
  - transitivity (X[f]Δ (d[X; 1; i] x.1)).
    + apply simplex_restrict_comp.
    + transitivity (X[f]Δ (simplex_constant X b 1)).
      * apply func_proper. exact (x.2 i).
      * apply simplex_constant_restrict.
Defined.

(** Evaluate at a spatial shape and an independently supplied time shape. *)

(** 在空间形状及独立给定的时间形状处求值。 *)

Definition two_sphere_cylinder_eval {x y : TwoSphereS X b}
    (H : TwoSphereCylinderHomotopy x y) {n : nat}
    (a : (@Hom Δ) n 2) (t : (@Hom Δ) n 1%nat)
  : X n
  := homotopy_map H.1 n
      (({|lower := a
         |} : D n),
        ({|lower := t
          |} :
          (Δ[1] : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)).

(** Equal shape operators give equal values, without comparing their records. *)

(** 相等形状算子给出相等的值，不比较算子记录。 *)

Lemma two_sphere_cylinder_eval_proper {x y : TwoSphereS X b}
    (H : TwoSphereCylinderHomotopy x y) {n : nat}
    (a a' : (@Hom Δ) n 2) (t t' : (@Hom Δ) n 1%nat)
    (E : a ≈ a') (F : t ≈ t')
  : two_sphere_cylinder_eval H a t ≈S two_sphere_cylinder_eval H a' t'.
Proof.
  apply (@func_proper _ _ (homotopy_map H.1 n)).
  split.
  - exact {|lower := E
           |}.
  - exact {|lower := F
           |}.
Defined.

(** Naturality restricts both coordinates together. *)

(** 自然性同时限制两个坐标。 *)

Lemma two_sphere_cylinder_restrict {x y : TwoSphereS X b}
    (H : TwoSphereCylinderHomotopy x y) {m n : nat}
    (θ : (@Hom Δ) m n) (a : (@Hom Δ) n 2) (t : (@Hom Δ) n 1%nat)
  : X[θ]Δ (two_sphere_cylinder_eval H a t) ≈S
      two_sphere_cylinder_eval H (a ∘ θ) (t ∘ θ).
Proof.
  symmetry. exact (simplex_restrict_natural (homotopy_map H.1) θ
    ({|lower := a
      |}, {|lower := t
            |})).
Defined.

(** The relative law applies to every spatial operator in the boundary. *)

(** 相对定律适用于边界中的每个空间算子。 *)

Definition two_sphere_cylinder_boundary {x y : TwoSphereS X b}
    (H : TwoSphereCylinderHomotopy x y) {n : nat}
    (a : (@Hom Δ) n 2) (t : (@Hom Δ) n 1%nat)
    (Ha : a ∈Sv BoundarySieve 2)
  : two_sphere_cylinder_eval H a t ≈S simplex_constant X b n
  := H.2 n {|lower := (a; Ha)
           |} {|lower := t
               |}.

(** Constant time at the generic triangle recovers its endpoint. *)

(** 在泛三角形处，常值时间恢复相应端点。 *)

Lemma two_sphere_cylinder_endpoint {x y : TwoSphereS X b}
    (H : TwoSphereCylinderHomotopy x y) (t : bool)
  : two_sphere_cylinder_eval H id
      (ConstF [Ord 2] (C := [Ord 1]) (simplex_interval_position t)) ≈S
      (if t then y.1 else x.1).
Proof.
  destruct t.
  - transitivity (X[(id : (@Hom Δ) 2 2)]Δ y.1).
    + exact (simplicial_homotopy_1 H.1 2 (simplex_generic 2)).
    + apply simplex_restrict_id.
  - transitivity (X[(id : (@Hom Δ) 2 2)]Δ x.1).
    + exact (simplicial_homotopy_0 H.1 2 (simplex_generic 2)).
    + apply simplex_restrict_id.
Defined.

End SphereCylinders.

(** ** The Three Tetrahedra of a Triangle Cylinder

    The kth tetrahedron repeats spatial vertex k and switches time after
    position k. Its four vertices follow the staircase through the prism.
    These are simplices of the actual product cylinder, not a geometric
    realization or a choice of a triangulation axiom. *)

(** ** 三角柱的三个四面体

    第 k 个四面体重复空间顶点 k，并在位置 k 之后切换时间。它的四个顶点
    沿棱柱中的阶梯行进。这些是实际积柱中的单形，不是几何实现，也不依赖
    选定三角剖分的公理。 *)

Program Definition two_sphere_prism_time (i : Ordinal 2)
  : (@Hom Δ) 3 1%nat
  := OrdinalF
      (λ j, simplex_interval_position (Nat.ltb (fin_rank i) (fin_rank j))) _.
Next Obligation.
  destruct i as [[] | [[] | [[] | []]]],
    x as [[] | [[] | [[] | [[] | []]]]],
    y as [[] | [[] | [[] | [[] | []]]]]; cbn in *; lia.
Defined.

(** ** Evaluating the Staircase

    Fix a relative cylinder with independent value sizes. The two internal
    triangles have times [001] and [011]. Its three tetrahedra connect
    these to the bottom and top triangles, with all side faces constant. *)

(** ** 求值阶梯

    固定值大小独立的相对柱。两个内部三角形的时间分别为 [001] 和 [011]。
    三个四面体将它们联系到底部及顶部三角形，全部侧面均为常值。 *)

Section SpherePrism.
Universes u p.
Context {X : Functor (Δ^op) SetCat@{u p _ _ _ _ _}} {b : X 0}
    {x y : TwoSphereS X b} (H : TwoSphereCylinderHomotopy X b x y).

(** The i-th actual tetrahedron of the staircase. *)

(** 阶梯中的第 i 个实际四面体。 *)

Definition two_sphere_prism (i : Ordinal 2)
  : X 3
  := two_sphere_cylinder_eval X b H σ[2; i] (two_sphere_prism_time i).

(** One of the two diagonal triangles, with time [001] or [011]. *)

(** 两个对角三角形之一，时间为 [001] 或 [011]。 *)

Definition two_sphere_cylinder_diagonal (i : Ordinal 1)
  : X 2
  := two_sphere_cylinder_eval X b H id σ[1; i].

(** All twelve faces are the endpoints, shared diagonals, or constant
    side faces. The table is in the original specified simplex equality. *)

(** 全部十二个面都是端点、共享对角面或常值侧面。表格使用原有指定单形相等。 *)

Lemma two_sphere_prism_faces (i : Ordinal 2) (j : Ordinal 3)
  : d[X; 2; j] (two_sphere_prism i) ≈S
      match fin_rank i, fin_rank j with
      | 0, 0 => y.1
      | 0, 1 => two_sphere_cylinder_diagonal fin_first⁺
      | 1, 1 => two_sphere_cylinder_diagonal fin_first⁺
      | 1, 2 => two_sphere_cylinder_diagonal fin_first
      | 2, 2 => two_sphere_cylinder_diagonal fin_first
      | 2, 3 => x.1
      | _, _ => simplex_constant X b 2
      end.
Proof.
  unfold two_sphere_prism.
  transitivity (two_sphere_cylinder_eval X b H
    (σ[2; i] ∘ δ[2; j]) (two_sphere_prism_time i ∘ δ[2; j])).
  - apply two_sphere_cylinder_restrict.
  - destruct i as [[] | [[] | [[] | []]]],
      j as [[] | [[] | [[] | [[] | []]]]];
      cbn [fin_rank two_sphere_cylinder_diagonal].
    all: try solve [apply two_sphere_cylinder_eval_proper;
      apply (snd (simplex_eq_iff _ _)); intros a;
      destruct a as [[] | [[] | [[] | []]]]; reflexivity].
    all: try solve [transitivity (two_sphere_cylinder_eval X b H id
        (ConstF [Ord 2] (C := [Ord 1]) (simplex_interval_position true)));
      [apply two_sphere_cylinder_eval_proper;
        apply (snd (simplex_eq_iff _ _)); intros a;
        destruct a as [[] | [[] | [[] | []]]]; reflexivity
      | exact (two_sphere_cylinder_endpoint X b H true)]].
    all: try solve [transitivity (two_sphere_cylinder_eval X b H id
        (ConstF [Ord 2] (C := [Ord 1]) (simplex_interval_position false)));
      [apply two_sphere_cylinder_eval_proper;
        apply (snd (simplex_eq_iff _ _)); intros a;
        destruct a as [[] | [[] | [[] | []]]]; reflexivity
      | exact (two_sphere_cylinder_endpoint X b H false)]].
    all: apply two_sphere_cylinder_boundary.
    all: first
      [apply (boundary_member_of_omission fin_first);
        intros [[] | [[] | [[] | []]]] E; discriminate E
      |apply (boundary_member_of_omission fin_first⁺);
        intros [[] | [[] | [[] | []]]] E; discriminate E
      |apply (boundary_member_of_omission fin_first⁺⁺);
        intros [[] | [[] | [[] | []]]] E; discriminate E].
Defined.

End SpherePrism.
