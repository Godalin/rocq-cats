From Cats Require Import
  Instance.Set.Simplicial.TriangleInput
  Instance.Set.Simplicial.TriangleIteration.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes for Initial-Region Gluing *)

(** ** Lower Equality Bounds

    Fix strictly distinct value and equality sizes, actual boundary and
    edge maps, and only their stated overlap equations. No Kan choices
    enter gluing; the final client separately supplies nine step choices. *)

Section lower_sizes.
Universes l u p.
Constraint l < u, u < p.
Context (r : Ordinal 2).
Context {X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}}.
Context (B : SimplicialParameterF (∂Δ[2]) 2 ⇒ X).
Context (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X).
Context (EB : triangle_input_boundary_agreement r B H).
Context (EH : triangle_input_face_agreement r H).

Definition lower_input
  : (TriangleHornStage r 0 : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X
  := TriangleInputN r B H EB EH.

Definition lower_cover
  := triangle_input_cover r.

Definition lower_compatibility
  := triangle_input_compatible r B H EB EH.

Definition lower_boundary n (a : (∂Δ[2]) n) (t : (Δ[2]) n)
  : lower_input n (triangle_input_generator r (inl (n; (a, t)))) ≈S
      B n (a, t)
  := triangle_input_boundary_β r B H EB EH n a t.

Definition lower_face j (Hj : ¬ j = r) n z
  : lower_input n
      (triangle_input_generator r (inr (j; (Hj, (n; z))))) ≈S H j n z
  := triangle_input_face_β r B H EB EH j Hj n z.

Definition lower_proper
    (B' : SimplicialParameterF (∂Δ[2]) 2 ⇒ X)
    (H' : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X)
    (EB' : triangle_input_boundary_agreement r B' H')
    (EH' : triangle_input_face_agreement r H')
    (E : B ≈N B') (F : ∀ j, ¬ j = r → H j ≈N H' j)
  : lower_input ≈N TriangleInputN r B' H' EB' EH'
  := triangle_input_proper r B B' H H' EB EH EB' EH' E F.

Definition lower_unique (a : TriangleHornStage r 0 ⇒ X)
    (E : ∀ n z, a n (triangle_input_generator r (inl (n; z))) ≈S B n z)
    (F : ∀ j (Hj : ¬ j = r) n z,
      a n (triangle_input_generator r (inr (j; (Hj, (n; z))))) ≈S H j n z)
  : a ≈N lower_input
  := triangle_input_unique r B H EB EH a E F.

Definition lower_nine_step_client
    (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s))
  : ∃ T : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X,
      (T ∘Nv RegionInclusionN (TriangleHornRegion r 0)) ≈N lower_input
  := TriangleHornProductExtension r K lower_input.

End lower_sizes.

(** ** Higher Equality Bounds

    Fix strictly distinct value and equality sizes, actual boundary and
    edge maps, and only their stated overlap equations. No Kan choices
    enter gluing; the final client separately supplies nine step choices. *)

Section higher_sizes.
Universes l u p.
Constraint l < u, u < p.
Context (r : Ordinal 2).
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (B : SimplicialParameterF (∂Δ[2]) 2 ⇒ X).
Context (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X).
Context (EB : triangle_input_boundary_agreement r B H).
Context (EH : triangle_input_face_agreement r H).

Definition higher_input
  : (TriangleHornStage r 0 : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X
  := TriangleInputN r B H EB EH.

Definition higher_cover
  := triangle_input_cover r.

Definition higher_compatibility
  := triangle_input_compatible r B H EB EH.

Definition higher_boundary n (a : (∂Δ[2]) n) (t : (Δ[2]) n)
  : higher_input n (triangle_input_generator r (inl (n; (a, t)))) ≈S
      B n (a, t)
  := triangle_input_boundary_β r B H EB EH n a t.

Definition higher_face j (Hj : ¬ j = r) n z
  : higher_input n
      (triangle_input_generator r (inr (j; (Hj, (n; z))))) ≈S H j n z
  := triangle_input_face_β r B H EB EH j Hj n z.

Definition higher_proper
    (B' : SimplicialParameterF (∂Δ[2]) 2 ⇒ X)
    (H' : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X)
    (EB' : triangle_input_boundary_agreement r B' H')
    (EH' : triangle_input_face_agreement r H')
    (E : B ≈N B') (F : ∀ j, ¬ j = r → H j ≈N H' j)
  : higher_input ≈N TriangleInputN r B' H' EB' EH'
  := triangle_input_proper r B B' H H' EB EH EB' EH' E F.

Definition higher_unique (a : TriangleHornStage r 0 ⇒ X)
    (E : ∀ n z, a n (triangle_input_generator r (inl (n; z))) ≈S B n z)
    (F : ∀ j (Hj : ¬ j = r) n z,
      a n (triangle_input_generator r (inr (j; (Hj, (n; z))))) ≈S H j n z)
  : a ≈N higher_input
  := triangle_input_unique r B H EB EH a E F.

Definition higher_nine_step_client
    (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s))
  : ∃ T : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X,
      (T ∘Nv RegionInclusionN (TriangleHornRegion r 0)) ≈N higher_input
  := TriangleHornProductExtension r K higher_input.

End higher_sizes.
