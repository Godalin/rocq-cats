From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereTriangleInput
  Instance.Set.Simplicial.TriangleIteration.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Lower Equality Bounds

    Keep strict independent sizes and arbitrary actual cylinders. Initial
    gluing needs no Kan choice; the final extension client supplies all nine. *)

(** * 较低相等界

    保留严格独立大小与任意实际柱；初始粘合无须Kan，末尾延拓客户端显式给出九选择。 *)

Section lower_sizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0).
Context (r : Ordinal 2).
Context (H K : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X).
Context (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j)).
Context (R' : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (K j)).
Context (E : cylinder_time_endpoint_matching r H).
Context (F : cylinder_time_endpoint_matching r K).

Definition lower_boundary
  : SimplicialParameterF (∂Δ[2]) 2 ⇒ X
  := SphereTriangleBoundaryN X b.

Definition lower_boundary_matching
  : triangle_input_boundary_agreement r (SphereTriangleBoundaryN X b) H
  := sphere_triangle_input_boundary_matching X b r H R.

Definition lower_input
  : TriangleHornStage r 0 ⇒ X
  := SphereTriangleInputN X b r H R E.

Definition lower_boundary_recovery n (a : (∂Δ[2]) n) (t : (Δ[2]) n)
  : lower_input n (triangle_input_generator r (inl (n; (a, t)))) ≈S
      simplex_constant X b n
  := sphere_triangle_input_boundary_β X b r H R E n a t.

Definition lower_face_recovery j (Hj : ¬ j = r) n z
  : lower_input n
      (triangle_input_generator r (inr (j; (Hj, (n; z))))) ≈S H j n z
  := sphere_triangle_input_face_β X b r H R E j Hj n z.

Definition lower_independent_witnesses (G : ∀ j, ¬ j = r → H j ≈N K j)
  : lower_input ≈N SphereTriangleInputN X b r K R' F
  := sphere_triangle_input_proper X b r H K R R' E F G.

Context {x y z : TwoSphereS X b}.
Context (C : TwoSphereCylinderHomotopy X b x y).
Context (D : TwoSphereCylinderHomotopy X b y z).

Definition lower_composite_edges
  : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X
  := SphereCompositeEdges X b C D.

Definition lower_composite_relative
  : ∀ j, ¬ j = fin_first⁺ →
      is_two_sphere_cylinder_relative X b (lower_composite_edges j)
  := sphere_composite_edges_relative X b C D.

Definition lower_composite_endpoints
  : cylinder_time_endpoint_matching fin_first⁺ lower_composite_edges
  := sphere_composite_edges_endpoints X b C D.

Definition lower_composite_initial
  : TriangleHornStage fin_first⁺ 0 ⇒ X
  := SphereCompositeTriangleInput X b C D.

Definition lower_reverse_edges
  : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X
  := SphereReverseEdges X b C.

Definition lower_reverse_relative
  : ∀ j, ¬ j = fin_first →
      is_two_sphere_cylinder_relative X b (lower_reverse_edges j)
  := sphere_reverse_edges_relative X b C.

Definition lower_reverse_endpoints
  : cylinder_time_endpoint_matching fin_first lower_reverse_edges
  := sphere_reverse_edges_endpoints X b C.

Definition lower_reverse_initial
  : TriangleHornStage fin_first 0 ⇒ X
  := SphereReverseTriangleInput X b C.

Definition lower_actual_extension_client
    (Q : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first s))
  : ∃ T : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X,
      (T ∘Nv RegionInclusionN (TriangleHornRegion fin_first 0)) ≈N
        lower_reverse_initial
  := TriangleHornProductExtension fin_first Q lower_reverse_initial.

End lower_sizes.

(** * Higher Equality Bounds

    Keep strict independent sizes and arbitrary actual cylinders. Initial
    gluing needs no Kan choice; the final extension client supplies all nine. *)

(** * 较高相等界

    保留严格独立大小与任意实际柱；初始粘合无须Kan，末尾延拓客户端显式给出九选择。 *)

Section higher_sizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (r : Ordinal 2).
Context (H K : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X).
Context (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j)).
Context (R' : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (K j)).
Context (E : cylinder_time_endpoint_matching r H).
Context (F : cylinder_time_endpoint_matching r K).

Definition higher_boundary
  : SimplicialParameterF (∂Δ[2]) 2 ⇒ X
  := SphereTriangleBoundaryN X b.

Definition higher_boundary_matching
  : triangle_input_boundary_agreement r (SphereTriangleBoundaryN X b) H
  := sphere_triangle_input_boundary_matching X b r H R.

Definition higher_input
  : TriangleHornStage r 0 ⇒ X
  := SphereTriangleInputN X b r H R E.

Definition higher_boundary_recovery n (a : (∂Δ[2]) n) (t : (Δ[2]) n)
  : higher_input n (triangle_input_generator r (inl (n; (a, t)))) ≈S
      simplex_constant X b n
  := sphere_triangle_input_boundary_β X b r H R E n a t.

Definition higher_face_recovery j (Hj : ¬ j = r) n z
  : higher_input n
      (triangle_input_generator r (inr (j; (Hj, (n; z))))) ≈S H j n z
  := sphere_triangle_input_face_β X b r H R E j Hj n z.

Definition higher_independent_witnesses (G : ∀ j, ¬ j = r → H j ≈N K j)
  : higher_input ≈N SphereTriangleInputN X b r K R' F
  := sphere_triangle_input_proper X b r H K R R' E F G.

Context {x y z : TwoSphereS X b}.
Context (C : TwoSphereCylinderHomotopy X b x y).
Context (D : TwoSphereCylinderHomotopy X b y z).

Definition higher_composite_edges
  : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X
  := SphereCompositeEdges X b C D.

Definition higher_composite_relative
  : ∀ j, ¬ j = fin_first⁺ →
      is_two_sphere_cylinder_relative X b (higher_composite_edges j)
  := sphere_composite_edges_relative X b C D.

Definition higher_composite_endpoints
  : cylinder_time_endpoint_matching fin_first⁺ higher_composite_edges
  := sphere_composite_edges_endpoints X b C D.

Definition higher_composite_initial
  : TriangleHornStage fin_first⁺ 0 ⇒ X
  := SphereCompositeTriangleInput X b C D.

Definition higher_reverse_edges
  : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X
  := SphereReverseEdges X b C.

Definition higher_reverse_relative
  : ∀ j, ¬ j = fin_first →
      is_two_sphere_cylinder_relative X b (higher_reverse_edges j)
  := sphere_reverse_edges_relative X b C.

Definition higher_reverse_endpoints
  : cylinder_time_endpoint_matching fin_first higher_reverse_edges
  := sphere_reverse_edges_endpoints X b C.

Definition higher_reverse_initial
  : TriangleHornStage fin_first 0 ⇒ X
  := SphereReverseTriangleInput X b C.

Definition higher_actual_extension_client
    (Q : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing fin_first s))
  : ∃ T : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X,
      (T ∘Nv RegionInclusionN (TriangleHornRegion fin_first 0)) ≈N
        higher_reverse_initial
  := TriangleHornProductExtension fin_first Q higher_reverse_initial.

End higher_sizes.
