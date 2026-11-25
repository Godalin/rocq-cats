From Cats Require Import
  Instance.Set.Simplicial.TriangleIteration.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Value and Equality Bounds *)

(** * 独立的取值和相等界 *)

(** ** Lower Equality Witnesses

    Fix strictly distinct bounds with smaller equality witnesses.
    Only the nine actual step choices are provided, without full Kan
    or equations between the selecting operations. *)

(** ** 较小的相等见证

    固定严格不同的大小，只给定九份实际步骤选择，不要求完整 Kan 或选择操作
    之间的方程。 *)

Section lower_sizes.
Universes l u p.
Constraint l < u, u < p.
Context (r : Ordinal 2).
Context {X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}}.
Context (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing r s)).
Context (a : TriangleHornStage r 0 ⇒ X).

Definition lower_chain
  : Chain (FctCat (Δ^op) SetCat@{u l _ _ _ _ _}) 9
  := TriangleHornChain r.

Definition lower_coordinates (i j : Ordinal 9) (f : (@Hom [Ord 9]) i j)
  : (RegionInclusionN (TriangleHornRegion r (fin_rank j)) ∘Nv
      chain_segment lower_chain i j f) ≈N
      RegionInclusionN (TriangleHornRegion r (fin_rank i))
  := triangle_horn_chain_segment_comm r i j f.

Definition lower_initial
  : (((TriangleHornFinalN r :
      (TriangleHornAmbient : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒
        TriangleHornStage r 9) ∘Nv
      RegionInclusionN (TriangleHornRegion r 0))) ≈N
      chain_segment lower_chain fin_first (fin_first⁺⁺⁺⁺⁺⁺⁺⁺⁺)
        (ordinal_from_first (fin_first⁺⁺⁺⁺⁺⁺⁺⁺⁺))
  := triangle_horn_initial_segment r.

Definition lower_iteration
  := triangle_horn_chain_extension_target r K a.

Definition lower_product
  : ∃ b : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ⇒ X,
      (b ∘Nv RegionInclusionN (TriangleHornRegion r 0)) ≈N a
  := TriangleHornProductExtension r K a.

Definition lower_recovery
  := lower_product.2.

End lower_sizes.

(** ** Higher Equality Witnesses

    Fix strictly distinct bounds with larger equality witnesses.
    Only the nine actual step choices are provided, without full Kan
    or equations between the selecting operations. *)

(** ** 较大的相等见证

    固定严格不同的大小，只给定九份实际步骤选择，不要求完整 Kan 或选择操作
    之间的方程。 *)

Section higher_sizes.
Universes l u p.
Constraint l < u, u < p.
Context (r : Ordinal 2).
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (K : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
    (simplex_triangle_horn_missing r s)).
Context (a : TriangleHornStage r 0 ⇒ X).

Definition higher_chain
  : Chain (FctCat (Δ^op) SetCat@{u p _ _ _ _ _}) 9
  := TriangleHornChain r.

Definition higher_coordinates (i j : Ordinal 9) (f : (@Hom [Ord 9]) i j)
  : (RegionInclusionN (TriangleHornRegion r (fin_rank j)) ∘Nv
      chain_segment higher_chain i j f) ≈N
      RegionInclusionN (TriangleHornRegion r (fin_rank i))
  := triangle_horn_chain_segment_comm r i j f.

Definition higher_initial
  : (((TriangleHornFinalN r :
      (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
        TriangleHornStage r 9) ∘Nv
      RegionInclusionN (TriangleHornRegion r 0))) ≈N
      chain_segment higher_chain fin_first (fin_first⁺⁺⁺⁺⁺⁺⁺⁺⁺)
        (ordinal_from_first (fin_first⁺⁺⁺⁺⁺⁺⁺⁺⁺))
  := triangle_horn_initial_segment r.

Definition higher_iteration
  := triangle_horn_chain_extension_target r K a.

Definition higher_product
  : ∃ b : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X,
      (b ∘Nv RegionInclusionN (TriangleHornRegion r 0)) ≈N a
  := TriangleHornProductExtension r K a.

Definition higher_recovery
  := higher_product.2.

End higher_sizes.
