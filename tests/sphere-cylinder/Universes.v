From Cats Require Import
  Instance.Set.Simplicial.Cocycle.SphereCylinder.

Local Open Scope nat_scope.

(** * Relative Cylinders at Independent Sizes

    The ambient simplex sizes and the coefficient sizes may have opposite
    strict orders. The comparison does not resize retained cylinder maps
    or force the generated class witnesses into the original equality bound. *)

(** * 独立大小中的相对柱

    环境单形大小及系数大小可以具有相反的严格次序。比较不重设保留柱映射的
    大小，也不迫使生成类见证进入原有相等界。 *)

Section CoefficientSizes.
Universes e h l u p.
Constraint e < h, h < l, l < u, u < p.
Context (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Monoid M} `{HN : !Monoid N}.

(** Lower native and lower ambient equality. *)

(** 较低原生相等及较低环境相等。 *)

Definition lower_native_lower_ambient_cylinder
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereCylinderHomotopy _ _ x y ↔ x ≈S y
  := cocycle_two_sphere_cylinder_iff x y.

(** Lower native and higher ambient equality. *)

(** 较低原生相等及较高环境相等。 *)

Definition lower_native_higher_ambient_cylinder
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereCylinderHomotopy _ _ x y ↔ x ≈S y
  := cocycle_two_sphere_cylinder_iff x y.

(** Higher native and lower ambient equality. *)

(** 较高原生相等及较低环境相等。 *)

Definition higher_native_lower_ambient_cylinder
    (x y : TwoSphereClassS
      (Z²(N) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : TwoSphereCylinderHomotopy _ _ x y ↔ x ≈S y
  := cocycle_two_sphere_cylinder_iff x y.

(** Higher native and higher ambient equality. *)

(** 较高原生相等及较高环境相等。 *)

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

(** ** 不带系数的通用柱

    对任意单纯广集，原生相等本身即给出相对柱。这些接口检查两种严格环境
    次序，不预设系数模型或 Kan 填充。 *)

Section GenericSizes.
Universes l u p.
Constraint l < u, u < p.

(** Lower ambient equality accepts the generic constant-cylinder map. *)

(** 较低环境相等接受通用常值柱映射。 *)

Definition lower_ambient_constant_cylinder
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (E : x ≈S y)
  : TwoSphereCylinderHomotopy X b x y
  := TwoSphereConstantCylinder X b x y E.

(** Higher ambient equality accepts the same transparent construction. *)

(** 较高环境相等接受同一个透明构造。 *)

Definition higher_ambient_constant_cylinder
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y : TwoSphereS X b) (E : x ≈S y)
  : TwoSphereCylinderHomotopy X b x y
  := TwoSphereConstantCylinder X b x y E.

End GenericSizes.
