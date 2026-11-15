From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereElementaryCylinder.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Strict Universes for the Elementary Cylinder *)

(** * 初等柱的严格宇宙 *)

(** ** Lower Equality Bounds Without Choices

    Keep carrier and equality sizes distinct. A supplied elementary
    tetrahedron determines the actual cylinder in the reversed endpoint
    order; neither horn selection nor algebra structure is available. *)

(** ** 较低相等界与无选择构造

    保持载体、相等大小不同。给定初等四面体确定实际柱，端点顺序反转；
    不提供 horn 选择或代数结构。 *)

Section lowerSizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0).
Context (x y : TwoSphereS X b) (H : TwoSphereHomotopy X b x y).

Definition lower_values
  : Ordinal 2 → X 3
  := two_sphere_homotopy_prism X b H.

Definition lower_faces (i : Ordinal 2) (j : Ordinal 3)
  := two_sphere_homotopy_prism_faces X b H i j.

Definition lower_adjacent (i : Ordinal 1)
  := two_sphere_homotopy_prism_adjacent X b H i.

Definition lower_relative
  : is_two_sphere_prism_relative X b lower_values
  := two_sphere_homotopy_prism_relative X b H.

Definition lower_cylinder
  : TwoSphereCylinderHomotopy X b y x
  := TwoSphereHomotopyCylinder X b H.

Definition lower_original_tetrahedron
  : simplex_prism_eval (homotopy_map lower_cylinder.1) fin_first⁺⁺ ≈S H.1
  := two_sphere_homotopy_cylinder_prism X b H fin_first⁺⁺.

Definition lower_values_proper (x' y' : TwoSphereS X b)
    (H' : TwoSphereHomotopy X b x' y') (E : x ≈S x') (W : H.1 ≈S H'.1)
  : ∀ i, two_sphere_homotopy_prism X b H i ≈S
      two_sphere_homotopy_prism X b H' i
  := two_sphere_homotopy_prism_proper X b H H' E W.

Definition lower_map_proper (x' y' : TwoSphereS X b)
    (H' : TwoSphereHomotopy X b x' y') (E : x ≈S x') (W : H.1 ≈S H'.1)
  : homotopy_map lower_cylinder.1 ≈N
      homotopy_map (TwoSphereHomotopyCylinder X b H').1
  := two_sphere_homotopy_cylinder_map_proper X b H H' E W.

End lowerSizes.

(** ** Higher Equality Bounds Without Choices

    Keep carrier and equality sizes distinct. A supplied elementary
    tetrahedron determines the actual cylinder in the reversed endpoint
    order; neither horn selection nor algebra structure is available. *)

(** ** 较高相等界与无选择构造

    保持载体、相等大小不同。给定初等四面体确定实际柱，端点顺序反转；
    不提供 horn 选择或代数结构。 *)

Section higherSizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (x y : TwoSphereS X b) (H : TwoSphereHomotopy X b x y).

Definition higher_values
  : Ordinal 2 → X 3
  := two_sphere_homotopy_prism X b H.

Definition higher_faces (i : Ordinal 2) (j : Ordinal 3)
  := two_sphere_homotopy_prism_faces X b H i j.

Definition higher_adjacent (i : Ordinal 1)
  := two_sphere_homotopy_prism_adjacent X b H i.

Definition higher_relative
  : is_two_sphere_prism_relative X b higher_values
  := two_sphere_homotopy_prism_relative X b H.

Definition higher_cylinder
  : TwoSphereCylinderHomotopy X b y x
  := TwoSphereHomotopyCylinder X b H.

Definition higher_original_tetrahedron
  : simplex_prism_eval (homotopy_map higher_cylinder.1) fin_first⁺⁺ ≈S H.1
  := two_sphere_homotopy_cylinder_prism X b H fin_first⁺⁺.

Definition higher_values_proper (x' y' : TwoSphereS X b)
    (H' : TwoSphereHomotopy X b x' y') (E : x ≈S x') (W : H.1 ≈S H'.1)
  : ∀ i, two_sphere_homotopy_prism X b H i ≈S
      two_sphere_homotopy_prism X b H' i
  := two_sphere_homotopy_prism_proper X b H H' E W.

Definition higher_map_proper (x' y' : TwoSphereS X b)
    (H' : TwoSphereHomotopy X b x' y') (E : x ≈S x') (W : H.1 ≈S H'.1)
  : homotopy_map higher_cylinder.1 ≈N
      homotopy_map (TwoSphereHomotopyCylinder X b H').1
  := two_sphere_homotopy_cylinder_map_proper X b H H' E W.

End higherSizes.
