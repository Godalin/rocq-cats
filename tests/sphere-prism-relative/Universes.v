From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SpherePrismRelative.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Relative Reconstruction Without Kan at Strict Sizes *)

(** * 严格大小下无需 Kan 的相对重构 *)

(** ** lower Equality Bounds

    Fix independent carrier/equality bounds, with no filling or algebra
    choices. All-degree relativity and finite side conditions keep Type
    witnesses; the cylinder map keeps its actual triangle gluing. *)

(** ** 较低相等界

    固定独立载体／相等界，无填充或代数选择。每维相对性及有限侧面条件保留
    Type 见证；柱映射保留实际三角柱粘合。 *)

Section lowerSizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0).
Let Q
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := SimplicialCylinderF (Δ[2] : Fct (Δ^op) SetCat@{u l _ _ _ _ _}).

(** The criterion applies to arbitrary maps, before endpoints are supplied. *)

(** 判据适用于任意映射，不预先要求端点。 *)

Definition lower_boundary (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      ∀ j k, two_sphere_boundary_prism_value X K j k ≈S simplex_constant X b 2
  := two_sphere_cylinder_relative_iff X b K.

(** Both shape coordinates identify the actual external coface. *)

(** 两个形状坐标确定实际外侧余面。 *)

Definition lower_faces (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      is_two_sphere_prism_relative X b (λ i, simplex_prism_eval K i)
  := two_sphere_prism_relative_iff X b K.

(** Finite relative witnesses transport along specified value equality. *)

(** 有限相对见证沿指定值相等运输。 *)

Definition lower_resp (a a' : Ordinal 2 → X 3) (E : ∀ i, a i ≈S a' i)
  : is_two_sphere_prism_relative X b a ↔ is_two_sphere_prism_relative X b a'
  := two_sphere_prism_relative_resp X b a a' E.

(** The two outer endpoint faces need no relative hypothesis. *)

(** 两个外侧端点面无需相对假设。 *)

Definition lower_endpoint (K : Q ⇒ X) (t : bool)
  : simplex_element_resp (K ∘Nv SimplicialEndpointN (Δ[2]) t) ≈S
      if t then d[X; 2; fin_first] (simplex_prism_eval K fin_first)
      else d[X; 2; fin_first⁺⁺⁺] (simplex_prism_eval K fin_first⁺⁺)
  := simplex_triangle_prism_endpoint K t.

(** The complete relative condition for gluing is exactly the six faces. *)

(** 粘合的完整相对条件恰为六个面。 *)

Definition lower_gluing (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  : is_two_sphere_cylinder_relative X b (SimplexTrianglePrismGluingN a H0 H1)
      ↔ is_two_sphere_prism_relative X b a
  := two_sphere_prism_gluing_relative_iff X b a H0 H1.

(** No three- or four-dimensional horn selection occurs. *)

(** 不含三维或四维 horn 选择。 *)

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

(** 端点及侧面证明字段不改变实际映射表达式。 *)

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

(** 恢复比较映射，不比较端点或相对定律记录。 *)

Definition lower_recovery (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
  : homotopy_map (SpherePrismReconstruct X b H).1 ≈N homotopy_map H.1
  := two_sphere_prism_reconstruct_map X b H.

End lowerSizes.

(** ** higher Equality Bounds

    Fix independent carrier/equality bounds, with no filling or algebra
    choices. All-degree relativity and finite side conditions keep Type
    witnesses; the cylinder map keeps its actual triangle gluing. *)

(** ** 较高相等界

    固定独立载体／相等界，无填充或代数选择。每维相对性及有限侧面条件保留
    Type 见证；柱映射保留实际三角柱粘合。 *)

Section higherSizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Let Q
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := SimplicialCylinderF (Δ[2] : Fct (Δ^op) SetCat@{u p _ _ _ _ _}).

(** The criterion applies to arbitrary maps, before endpoints are supplied. *)

(** 判据适用于任意映射，不预先要求端点。 *)

Definition higher_boundary (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      ∀ j k, two_sphere_boundary_prism_value X K j k ≈S simplex_constant X b 2
  := two_sphere_cylinder_relative_iff X b K.

(** Both shape coordinates identify the actual external coface. *)

(** 两个形状坐标确定实际外侧余面。 *)

Definition higher_faces (K : Q ⇒ X)
  : is_two_sphere_cylinder_relative X b K ↔
      is_two_sphere_prism_relative X b (λ i, simplex_prism_eval K i)
  := two_sphere_prism_relative_iff X b K.

(** Finite relative witnesses transport along specified value equality. *)

(** 有限相对见证沿指定值相等运输。 *)

Definition higher_resp (a a' : Ordinal 2 → X 3) (E : ∀ i, a i ≈S a' i)
  : is_two_sphere_prism_relative X b a ↔ is_two_sphere_prism_relative X b a'
  := two_sphere_prism_relative_resp X b a a' E.

(** The two outer endpoint faces need no relative hypothesis. *)

(** 两个外侧端点面无需相对假设。 *)

Definition higher_endpoint (K : Q ⇒ X) (t : bool)
  : simplex_element_resp (K ∘Nv SimplicialEndpointN (Δ[2]) t) ≈S
      if t then d[X; 2; fin_first] (simplex_prism_eval K fin_first)
      else d[X; 2; fin_first⁺⁺⁺] (simplex_prism_eval K fin_first⁺⁺)
  := simplex_triangle_prism_endpoint K t.

(** The complete relative condition for gluing is exactly the six faces. *)

(** 粘合的完整相对条件恰为六个面。 *)

Definition higher_gluing (a : Ordinal 2 → X 3)
    (H0 : d[X; 2; fin_first⁺] (a fin_first) ≈S
      d[X; 2; fin_first⁺] (a fin_first⁺))
    (H1 : d[X; 2; fin_first⁺⁺] (a fin_first⁺) ≈S
      d[X; 2; fin_first⁺⁺] (a fin_first⁺⁺))
  : is_two_sphere_cylinder_relative X b (SimplexTrianglePrismGluingN a H0 H1)
      ↔ is_two_sphere_prism_relative X b a
  := two_sphere_prism_gluing_relative_iff X b a H0 H1.

(** No three- or four-dimensional horn selection occurs. *)

(** 不含三维或四维 horn 选择。 *)

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

(** 端点及侧面证明字段不改变实际映射表达式。 *)

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

(** 恢复比较映射，不比较端点或相对定律记录。 *)

Definition higher_recovery (x y : TwoSphereS X b)
    (H : TwoSphereCylinderHomotopy X b x y)
  : homotopy_map (SpherePrismReconstruct X b H).1 ≈N homotopy_map H.1
  := two_sphere_prism_reconstruct_map X b H.

End higherSizes.
