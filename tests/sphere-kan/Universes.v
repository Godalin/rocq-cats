From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereKan.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes and Minimal Three-Horn Choices

    Every operation accepts only its required horn selection. The probes
    keep ambient equality strictly below or above simplex carriers, without
    shrinking retained tetrahedra or requiring full Kan choices. *)

(** * 独立大小与最小三维 Horn 选择

    每个运算只接受其所需的 horn 选择。检查使环境相等严格低于或高于单形
    载体，不缩小保留四面体，也不要求完整 Kan 选择。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Actual gluing at lower ambient equality. *)

(** 此环境相等配置中的实际粘合。 *)

Definition lower_horn
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (i : Ordinal 3) (a : Ordinal 3 → TwoSphereS X b)
  : HornS X 3 i
  := SphereTetrahedronHornN X b i a.

(** Composite only needs missing face 2, at lower equality. *)

(** 此相等配置下的构造仅要求缺失面 2。 *)

Definition lower_composite
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺⁺}
    (x y : TwoSphereS X b)
  : ∃ z : TwoSphereS X b, TwoSphereComposite X b x y z
  := SphereKanComposite X b x y.

(** RightInverse only needs missing face 1, at lower equality. *)

(** 此相等配置下的构造仅要求缺失面 1。 *)

Definition lower_rightinverse
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b x y (two_sphere_base X b)
  := SphereKanRightInverse X b x.

(** LeftInverse only needs missing face 3, at lower equality. *)

(** 此相等配置下的构造仅要求缺失面 3。 *)

Definition lower_leftinverse
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺⁺⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b y x (two_sphere_base X b)
  := SphereKanLeftInverse X b x.

(** Actual gluing at higher ambient equality. *)

(** 此环境相等配置中的实际粘合。 *)

Definition higher_horn
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (i : Ordinal 3) (a : Ordinal 3 → TwoSphereS X b)
  : HornS X 3 i
  := SphereTetrahedronHornN X b i a.

(** Composite only needs missing face 2, at higher equality. *)

(** 此相等配置下的构造仅要求缺失面 2。 *)

Definition higher_composite
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺⁺}
    (x y : TwoSphereS X b)
  : ∃ z : TwoSphereS X b, TwoSphereComposite X b x y z
  := SphereKanComposite X b x y.

(** RightInverse only needs missing face 1, at higher equality. *)

(** 此相等配置下的构造仅要求缺失面 1。 *)

Definition higher_rightinverse
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b x y (two_sphere_base X b)
  := SphereKanRightInverse X b x.

(** LeftInverse only needs missing face 3, at higher equality. *)

(** 此相等配置下的构造仅要求缺失面 3。 *)

Definition higher_leftinverse
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX : !HasHornFillers X 3 fin_first⁺⁺⁺}
    (x : TwoSphereS X b)
  : ∃ y : TwoSphereS X b,
      TwoSphereComposite X b y x (two_sphere_base X b)
  := SphereKanLeftInverse X b x.

End StrictSizes.
