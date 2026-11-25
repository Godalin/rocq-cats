From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderClass.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independently Sized Relative Cylinders

    Construct diagonal boundaries and all three actual prism witnesses
    without selections. Descent uses only dimension-four missing faces
    one/two, with simplex equality strictly below or above its carrier. *)

(** * 大小独立的相对柱

    构造对角边界及三个实际棱柱见证无需选择。下降只使用四维缺第一／第二面，
    单形相等严格低于或高于载体。 *)

(** ** Strict Profiles with No Three-Dimensional Choices

    Fix three strictly increasing universes. Every signature states its
    exact choices; no selected multiplication or full Kan is available. *)

(** ** 无三维选择的严格配置

    固定三个严格递增宇宙。每个签名明确列出所需选择，不提供选定乘法或完整 Kan。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** All restricted diagonal edges are constant without choices. *)

(** 无需选择即可证明对角面的所有限制边为常值。 *)

Definition lower_boundary
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (i : Ordinal 1) (j : Ordinal 2)
  : d[X; 1; j] (two_sphere_cylinder_diagonal H i) ≈S
      simplex_constant X b 1
  := two_sphere_cylinder_diagonal_boundary X b H i j.

(** The actual triangle is retained in the sphere subset. *)

(** 球面子集中保留实际三角形。 *)

Definition lower_diagonal
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (i : Ordinal 1)
  : TwoSphereS X b
  := TwoSphereCylinderDiagonal X b H i.

(** The first witness requires no Kan structure. *)

(** 第一个见证不要求 Kan 结构。 *)

Definition lower_first
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereLowHomotopy X b y (TwoSphereCylinderDiagonal X b H fin_first⁺)
  := SphereCylinderFirstLowHomotopy X b H.

(** The middle is an unselected actual composite with constant first input. *)

(** 中间是未作选择的实际合成，第一输入为常值。 *)

Definition lower_middle
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereComposite X b (two_sphere_base X b)
      (TwoSphereCylinderDiagonal X b H fin_first⁺)
      (TwoSphereCylinderDiagonal X b H fin_first)
  := SphereCylinderMiddleComposite X b H.

(** The last tetrahedron is a standard elementary homotopy. *)

(** 最后一块四面体为标准初等同伦。 *)

Definition lower_last
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereHomotopy X b (TwoSphereCylinderDiagonal X b H fin_first) x
  := SphereCylinderLastHomotopy X b H.

(** Only the two four-dimensional selections enter descent. *)

(** 下降只带有这两项四维选择。 *)

Definition lower_descent
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
  : (x : TwoSphereClassS X b) ≈S y
  := two_sphere_cylinder_class X b H.

(** All restricted diagonal edges are constant without choices. *)

(** 无需选择即可证明对角面的所有限制边为常值。 *)

Definition higher_boundary
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (i : Ordinal 1) (j : Ordinal 2)
  : d[X; 1; j] (two_sphere_cylinder_diagonal H i) ≈S
      simplex_constant X b 1
  := two_sphere_cylinder_diagonal_boundary X b H i j.

(** The actual triangle is retained in the sphere subset. *)

(** 球面子集中保留实际三角形。 *)

Definition higher_diagonal
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (i : Ordinal 1)
  : TwoSphereS X b
  := TwoSphereCylinderDiagonal X b H i.

(** The first witness requires no Kan structure. *)

(** 第一个见证不要求 Kan 结构。 *)

Definition higher_first
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereLowHomotopy X b y (TwoSphereCylinderDiagonal X b H fin_first⁺)
  := SphereCylinderFirstLowHomotopy X b H.

(** The middle is an unselected actual composite with constant first input. *)

(** 中间是未作选择的实际合成，第一输入为常值。 *)

Definition higher_middle
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereComposite X b (two_sphere_base X b)
      (TwoSphereCylinderDiagonal X b H fin_first⁺)
      (TwoSphereCylinderDiagonal X b H fin_first)
  := SphereCylinderMiddleComposite X b H.

(** The last tetrahedron is a standard elementary homotopy. *)

(** 最后一块四面体为标准初等同伦。 *)

Definition higher_last
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereHomotopy X b (TwoSphereCylinderDiagonal X b H fin_first) x
  := SphereCylinderLastHomotopy X b H.

(** Only the two four-dimensional selections enter descent. *)

(** 下降只带有这两项四维选择。 *)

Definition higher_descent
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
  : (x : TwoSphereClassS X b) ≈S y
  := two_sphere_cylinder_class X b H.

End StrictSizes.
