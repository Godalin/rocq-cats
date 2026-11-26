From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderKan.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

Local Opaque sphere_triangle_extension_recovery SphereTriangleInputN
  SphereRelativeTriangleExtension SphereCylinderComposite SphereCylinderReverse.

(** * Lower Equality Bounds

    Keep strict independent sizes. Recovery assumes only an actual map and
    its equation; construction supplies precisely the nine stated choices. *)

Section lower_sizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0).
Context (r : Ordinal 2).
Context (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X).
Context (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j)).
Context (E : cylinder_time_endpoint_matching r H).

(** Keep recovery as a function of the actual map and its restriction
    equation; the selected constructor below consumes that function. *)

Definition lower_recovery
  := sphere_triangle_extension_recovery X b r H R E.

Context (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing r s)).

Definition lower_extension
  : ∃ Q : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X,
      (is_two_sphere_triangle_relative X b Q *
        (∀ j, ¬ j = r → simplicial_triangle_edge Q j ≈N H j))%type
  := SphereRelativeTriangleExtension X b r K H R E.

Definition lower_full_relative
  : is_two_sphere_triangle_relative X b lower_extension.1
  := fst lower_extension.2.

Definition lower_retained_edge j (Hj : ¬ j = r)
  : simplicial_triangle_edge lower_extension.1 j ≈N H j
  := snd lower_extension.2 j Hj.

Context {x y z : TwoSphereS X b}.
Context (A : TwoSphereCylinderHomotopy X b x y).
Context (B : TwoSphereCylinderHomotopy X b y z).
Context (C : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing fin_first⁺ s)).
Context (D : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing fin_first s)).

Definition lower_composite
  : TwoSphereCylinderHomotopy X b x z
  := SphereCylinderComposite X b C A B.

Definition lower_reverse
  : TwoSphereCylinderHomotopy X b y x
  := SphereCylinderReverse X b D A.

Definition lower_composite_map
  := sphere_cylinder_composite_map X b C A B.

Definition lower_reverse_map
  := sphere_cylinder_reverse_map X b D A.

Definition lower_reverse_initial_endpoint
  : (homotopy_map lower_reverse.1 ∘Nv SimplicialEndpointN (Δ[2]) false)
      ≈N ⟦y.1⟧Δ[X; 2]
  := simplicial_homotopy_0 lower_reverse.1.

Definition lower_reverse_final_endpoint
  : (homotopy_map lower_reverse.1 ∘Nv SimplicialEndpointN (Δ[2]) true)
      ≈N ⟦x.1⟧Δ[X; 2]
  := simplicial_homotopy_1 lower_reverse.1.

Definition lower_explicit_full_Kan_reverse (HK : HasKanFillers X)
  : TwoSphereCylinderHomotopy X b y x
  := SphereCylinderReverse X b
      (λ s, @hasHornFillers X HK (simplex_triangle_horn_face_dim s)
        (simplex_triangle_horn_missing fin_first s)) A.

Definition lower_explicit_full_Kan_composite (HK : HasKanFillers X)
  : TwoSphereCylinderHomotopy X b x z
  := SphereCylinderComposite X b
      (λ s, @hasHornFillers X HK (simplex_triangle_horn_face_dim s)
        (simplex_triangle_horn_missing fin_first⁺ s)) A B.

End lower_sizes.

(** * Higher Equality Bounds

    Keep strict independent sizes. Recovery assumes only an actual map and
    its equation; construction supplies precisely the nine stated choices. *)

Section higher_sizes.
Universes l u p.
Constraint l < u, u < p.
Context (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0).
Context (r : Ordinal 2).
Context (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X).
Context (R : ∀ j, ¬ j = r → is_two_sphere_cylinder_relative X b (H j)).
Context (E : cylinder_time_endpoint_matching r H).

(** Keep recovery as a function of the actual map and its restriction
    equation; the selected constructor below consumes that function. *)

Definition higher_recovery
  := sphere_triangle_extension_recovery X b r H R E.

Context (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing r s)).

Definition higher_extension
  : ∃ Q : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X,
      (is_two_sphere_triangle_relative X b Q *
        (∀ j, ¬ j = r → simplicial_triangle_edge Q j ≈N H j))%type
  := SphereRelativeTriangleExtension X b r K H R E.

Definition higher_full_relative
  : is_two_sphere_triangle_relative X b higher_extension.1
  := fst higher_extension.2.

Definition higher_retained_edge j (Hj : ¬ j = r)
  : simplicial_triangle_edge higher_extension.1 j ≈N H j
  := snd higher_extension.2 j Hj.

Context {x y z : TwoSphereS X b}.
Context (A : TwoSphereCylinderHomotopy X b x y).
Context (B : TwoSphereCylinderHomotopy X b y z).
Context (C : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing fin_first⁺ s)).
Context (D : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing fin_first s)).

Definition higher_composite
  : TwoSphereCylinderHomotopy X b x z
  := SphereCylinderComposite X b C A B.

Definition higher_reverse
  : TwoSphereCylinderHomotopy X b y x
  := SphereCylinderReverse X b D A.

Definition higher_composite_map
  := sphere_cylinder_composite_map X b C A B.

Definition higher_reverse_map
  := sphere_cylinder_reverse_map X b D A.

Definition higher_reverse_initial_endpoint
  : (homotopy_map higher_reverse.1 ∘Nv SimplicialEndpointN (Δ[2]) false)
      ≈N ⟦y.1⟧Δ[X; 2]
  := simplicial_homotopy_0 higher_reverse.1.

Definition higher_reverse_final_endpoint
  : (homotopy_map higher_reverse.1 ∘Nv SimplicialEndpointN (Δ[2]) true)
      ≈N ⟦x.1⟧Δ[X; 2]
  := simplicial_homotopy_1 higher_reverse.1.

Definition higher_explicit_full_Kan_reverse (HK : HasKanFillers X)
  : TwoSphereCylinderHomotopy X b y x
  := SphereCylinderReverse X b
      (λ s, @hasHornFillers X HK (simplex_triangle_horn_face_dim s)
        (simplex_triangle_horn_missing fin_first s)) A.

Definition higher_explicit_full_Kan_composite (HK : HasKanFillers X)
  : TwoSphereCylinderHomotopy X b x z
  := SphereCylinderComposite X b
      (λ s, @hasHornFillers X HK (simplex_triangle_horn_face_dim s)
        (simplex_triangle_horn_missing fin_first⁺ s)) A B.

End higher_sizes.

Local Transparent sphere_triangle_extension_recovery SphereTriangleInputN
  SphereRelativeTriangleExtension SphereCylinderComposite SphereCylinderReverse.
