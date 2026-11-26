From Cats Require Import
  Instance.Set.Simplicial.Cocycle.SphereCylinder.

Local Open Scope nat_scope.

(** * Relative Cylinders at Independent Sizes

    The ambient simplex sizes and the coefficient sizes may have opposite
    strict orders. The comparison does not resize retained cylinder maps
    or force the generated class witnesses into the original equality bound. *)

Section CoefficientSizes.
Universes e h l u p.
Constraint e < h, h < l, l < u, u < p.
Context (M : Monoid@{h e _}) (N : Monoid@{e h _}).

(** Lower native and lower ambient equality. *)

Definition lower_native_lower_ambient_cylinder
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereCylinderHomotopy _ _ x y ↔ x ≈S y
  := cocycle_two_sphere_cylinder_iff x y.

(** Lower native and higher ambient equality. *)

Definition lower_native_higher_ambient_cylinder
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereCylinderHomotopy _ _ x y ↔ x ≈S y
  := cocycle_two_sphere_cylinder_iff x y.

(** Higher native and lower ambient equality. *)

Definition higher_native_lower_ambient_cylinder
    (x y : TwoSphereClassS
      (Z²(N) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereCylinderHomotopy _ _ x y ↔ x ≈S y
  := cocycle_two_sphere_cylinder_iff x y.

(** Higher native and higher ambient equality. *)

Definition higher_native_higher_ambient_cylinder
    (x y : TwoSphereClassS
      (Z²(N) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereCylinderHomotopy _ _ x y ↔ x ≈S y
  := cocycle_two_sphere_cylinder_iff x y.

End CoefficientSizes.

(** ** Generic Cylinders without Coefficients

    Native equality alone gives a relative cylinder for an arbitrary
    simplicial setoid. These interfaces check both strict ambient orders
    without any assumption about a coefficient model or Kan fillers. *)

Section GenericSizes.
Universes l u p.
Constraint l < u, u < p.

(** Lower ambient equality accepts the generic constant-cylinder map. *)

Definition lower_ambient_constant_cylinder
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (E : x ≈S y)
  : TwoSphereCylinderHomotopy X b x y
  := TwoSphereConstantCylinder X b x y E.

(** Higher ambient equality accepts the same transparent construction. *)

Definition higher_ambient_constant_cylinder
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (E : x ≈S y)
  : TwoSphereCylinderHomotopy X b x y
  := TwoSphereConstantCylinder X b x y E.

End GenericSizes.
