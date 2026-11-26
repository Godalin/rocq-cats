From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderClass.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independently Sized Relative Cylinders

    Construct diagonal boundaries and all three actual prism witnesses
    without selections. Descent uses only dimension-four missing faces
    one/two, with simplex equality strictly below or above its carrier. *)

(** ** Strict Profiles with No Three-Dimensional Choices

    Fix three strictly increasing universes. Every signature states its
    exact choices; no selected multiplication or full Kan is available. *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** All restricted diagonal edges are constant without choices. *)

Definition lower_boundary
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (i : Ordinal 1) (j : Ordinal 2)
  : d[X; 1; j] (two_sphere_cylinder_diagonal H i) ≈S
      simplex_constant X b 1
  := two_sphere_cylinder_diagonal_boundary X b H i j.

(** The actual triangle is retained in the sphere subset. *)

Definition lower_diagonal
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (i : Ordinal 1)
  : TwoSphereS X b
  := TwoSphereCylinderDiagonal X b H i.

(** The first witness requires no Kan structure. *)

Definition lower_first
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereLowHomotopy X b y (TwoSphereCylinderDiagonal X b H fin_first⁺)
  := SphereCylinderFirstLowHomotopy X b H.

(** The middle is an unselected actual composite with constant first input. *)

Definition lower_middle
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereComposite X b (two_sphere_base X b)
      (TwoSphereCylinderDiagonal X b H fin_first⁺)
      (TwoSphereCylinderDiagonal X b H fin_first)
  := SphereCylinderMiddleComposite X b H.

(** The last tetrahedron is a standard elementary homotopy. *)

Definition lower_last
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereHomotopy X b (TwoSphereCylinderDiagonal X b H fin_first) x
  := SphereCylinderLastHomotopy X b H.

(** Only the two four-dimensional selections enter descent. *)

Definition lower_descent
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
  : (x : TwoSphereClassS X b) ≈S y
  := two_sphere_cylinder_class X b H.

(** All restricted diagonal edges are constant without choices. *)

Definition higher_boundary
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (i : Ordinal 1) (j : Ordinal 2)
  : d[X; 1; j] (two_sphere_cylinder_diagonal H i) ≈S
      simplex_constant X b 1
  := two_sphere_cylinder_diagonal_boundary X b H i j.

(** The actual triangle is retained in the sphere subset. *)

Definition higher_diagonal
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    (i : Ordinal 1)
  : TwoSphereS X b
  := TwoSphereCylinderDiagonal X b H i.

(** The first witness requires no Kan structure. *)

Definition higher_first
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereLowHomotopy X b y (TwoSphereCylinderDiagonal X b H fin_first⁺)
  := SphereCylinderFirstLowHomotopy X b H.

(** The middle is an unselected actual composite with constant first input. *)

Definition higher_middle
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereComposite X b (two_sphere_base X b)
      (TwoSphereCylinderDiagonal X b H fin_first⁺)
      (TwoSphereCylinderDiagonal X b H fin_first)
  := SphereCylinderMiddleComposite X b H.

(** The last tetrahedron is a standard elementary homotopy. *)

Definition higher_last
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
  : TwoSphereHomotopy X b (TwoSphereCylinderDiagonal X b H fin_first) x
  := SphereCylinderLastHomotopy X b H.

(** Only the two four-dimensional selections enter descent. *)

Definition higher_descent
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (H : TwoSphereCylinderHomotopy X b x y)
    `{HX1 : !HasHornFillers X 4 fin_first⁺}
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
  : (x : TwoSphereClassS X b) ≈S y
  := two_sphere_cylinder_class X b H.

End StrictSizes.
