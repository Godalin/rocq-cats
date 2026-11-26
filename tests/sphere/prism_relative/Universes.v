From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SpherePrismRelative.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Relative Reconstruction Without Kan at Strict Sizes *)

(** ** lower Equality Bounds

    Fix independent carrier/equality bounds, with no filling or algebra
    choices. All-degree relativity and finite side conditions keep Type
    witnesses; the cylinder map keeps its actual triangle gluing. *)

Section lowerSizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0).
Let Q
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := SimplicialCylinderF (Δ[2] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}).

(** The criterion applies to arbitrary maps, before endpoints are supplied. *)

Definition lower_boundary (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      ∀ j k, two_sphere_boundary_prism_value X K j k ≈S simplex_constant X b 2
  := two_sphere_cylinder_relative_iff X b K.

(** Both shape coordinates identify the actual external coface. *)

Definition lower_faces (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      is_two_sphere_prism_relative X b (λ i, simplex_prism_eval K i)
  := two_sphere_prism_relative_iff X b K.

(** Finite relative witnesses transport along specified value equality. *)

Definition lower_resp (a a' : Ordinal 2 → X 3) (E : ∀ i, a i ≈S a' i)
  : is_two_sphere_prism_relative X b a ↔ is_two_sphere_prism_relative X b a'
  := two_sphere_prism_relative_resp X b a a' E.

(** The two outer endpoint faces need no relative hypothesis. *)

Definition lower_endpoint (K : Q ⇒ X) (t : bool)
  : simplex_element_resp (K ∘Nv SimplicialEndpointN (Δ[2]) t) ≈S
      if t then d[X; 2; fin_first] (simplex_prism_eval K fin_first)
      else d[X; 2; fin_first⁺⁺⁺] (simplex_prism_eval K fin_first⁺⁺)
  := simplex_triangle_prism_endpoint K t.

(** The complete relative condition for gluing is exactly the six faces. *)

Definition lower_gluing (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  : is_two_sphere_cylinder_relative X b (SimplexTrianglePrismGluingN a H0 H1)
      ↔ is_two_sphere_prism_relative X b a
  := two_sphere_prism_gluing_relative_iff X b a H0 H1.

(** No three- or four-dimensional horn selection occurs. *)

Definition lower_cylinder (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
    (x y : TwoSphereS X b)
    (E0 : d[X; 2; fin_first⁺⁺⁺] (a fin_first⁺⁺) ≈S x.1)
    (E1 : d[X; 2; fin_first] (a fin_first) ≈S y.1)
    (R : is_two_sphere_prism_relative X b a)
  : TwoSphereCylinderHomotopy X b x y
  := SpherePrismCylinder X b a H0 H1 x y E0 E1 R.

(** Endpoint and side proof fields do not change the actual map expression. *)

Definition lower_map_conversion (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
    (x y : TwoSphereS X b)
    (E0 : d[X; 2; fin_first⁺⁺⁺] (a fin_first⁺⁺) ≈S x.1)
    (E1 : d[X; 2; fin_first] (a fin_first) ≈S y.1)
    (R : is_two_sphere_prism_relative X b a)
  : homotopy_map (lower_cylinder a H0 H1 x y E0 E1 R).1 =
      SimplexTrianglePrismGluingN a H0 H1
  := eq_refl.

(** Recovery compares maps, not endpoint or relative law records. *)

Definition lower_recovery (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
  : homotopy_map (SpherePrismReconstruct X b H).1 ≈N homotopy_map H.1
  := two_sphere_prism_reconstruct_map X b H.

End lowerSizes.

(** ** higher Equality Bounds

    Fix independent carrier/equality bounds, with no filling or algebra
    choices. All-degree relativity and finite side conditions keep Type
    witnesses; the cylinder map keeps its actual triangle gluing. *)

Section higherSizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Let Q
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialCylinderF (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

(** The criterion applies to arbitrary maps, before endpoints are supplied. *)

Definition higher_boundary (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      ∀ j k, two_sphere_boundary_prism_value X K j k ≈S simplex_constant X b 2
  := two_sphere_cylinder_relative_iff X b K.

(** Both shape coordinates identify the actual external coface. *)

Definition higher_faces (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      is_two_sphere_prism_relative X b (λ i, simplex_prism_eval K i)
  := two_sphere_prism_relative_iff X b K.

(** Finite relative witnesses transport along specified value equality. *)

Definition higher_resp (a a' : Ordinal 2 → X 3) (E : ∀ i, a i ≈S a' i)
  : is_two_sphere_prism_relative X b a ↔ is_two_sphere_prism_relative X b a'
  := two_sphere_prism_relative_resp X b a a' E.

(** The two outer endpoint faces need no relative hypothesis. *)

Definition higher_endpoint (K : Q ⇒ X) (t : bool)
  : simplex_element_resp (K ∘Nv SimplicialEndpointN (Δ[2]) t) ≈S
      if t then d[X; 2; fin_first] (simplex_prism_eval K fin_first)
      else d[X; 2; fin_first⁺⁺⁺] (simplex_prism_eval K fin_first⁺⁺)
  := simplex_triangle_prism_endpoint K t.

(** The complete relative condition for gluing is exactly the six faces. *)

Definition higher_gluing (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  : is_two_sphere_cylinder_relative X b (SimplexTrianglePrismGluingN a H0 H1)
      ↔ is_two_sphere_prism_relative X b a
  := two_sphere_prism_gluing_relative_iff X b a H0 H1.

(** No three- or four-dimensional horn selection occurs. *)

Definition higher_cylinder (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
    (x y : TwoSphereS X b)
    (E0 : d[X; 2; fin_first⁺⁺⁺] (a fin_first⁺⁺) ≈S x.1)
    (E1 : d[X; 2; fin_first] (a fin_first) ≈S y.1)
    (R : is_two_sphere_prism_relative X b a)
  : TwoSphereCylinderHomotopy X b x y
  := SpherePrismCylinder X b a H0 H1 x y E0 E1 R.

(** Endpoint and side proof fields do not change the actual map expression. *)

Definition higher_map_conversion (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
    (x y : TwoSphereS X b)
    (E0 : d[X; 2; fin_first⁺⁺⁺] (a fin_first⁺⁺) ≈S x.1)
    (E1 : d[X; 2; fin_first] (a fin_first) ≈S y.1)
    (R : is_two_sphere_prism_relative X b a)
  : homotopy_map (higher_cylinder a H0 H1 x y E0 E1 R).1 =
      SimplexTrianglePrismGluingN a H0 H1
  := eq_refl.

(** Recovery compares maps, not endpoint or relative law records. *)

Definition higher_recovery (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
  : homotopy_map (SpherePrismReconstruct X b H).1 ≈N homotopy_map H.1
  := two_sphere_prism_reconstruct_map X b H.

End higherSizes.
