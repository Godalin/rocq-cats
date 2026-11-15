From Cats Require Import
  Instance.Set.Simplicial.Homotopy.TimeOverlap
  Instance.Set.Simplicial.TriangleInput
  Instance.Set.Simplicial.TriangleIteration.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Lower Equality Bounds

    Source and target are arbitrary. Only endpoint compatibility is supplied;
    no Kan choice or equality of law witnesses enters the equivalence. *)

(** * 较小相等界

    源和目标任意，只给定端点相容；等价不使用 Kan 选择，也不等同定律见证。 *)

Section lower_sizes.
Universes l u p.
Constraint l < u, u < p.
Context {A X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}}.
Context (r : Ordinal 2).
Context (H K : Ordinal 2 → SimplicialCylinderF A ⇒ X).
Context (EP : cylinder_time_endpoint_matching r H).
Context (EF : cylinder_time_factor_matching r H).

Definition lower_forward
  : cylinder_time_factor_matching r H
  := cylinder_time_factors_from_endpoints r H EP.

Definition lower_backward
  : cylinder_time_endpoint_matching r H
  := cylinder_time_endpoints_from_factors r H EF.

Definition lower_iff
  : cylinder_time_endpoint_matching r H ↔ cylinder_time_factor_matching r H
  := cylinder_time_matching_iff r H.

Definition lower_proper (E : ∀ j, ¬ j = r → H j ≈N K j)
  : cylinder_time_factor_matching r H ↔ cylinder_time_factor_matching r K
  := cylinder_time_factor_matching_proper r H K E.

End lower_sizes.

(** * Higher Equality Bounds

    Source and target are arbitrary. Only endpoint compatibility is supplied;
    no Kan choice or equality of law witnesses enters the equivalence. *)

(** * 较大相等界

    源和目标任意，只给定端点相容；等价不使用 Kan 选择，也不等同定律见证。 *)

Section higher_sizes.
Universes l u p.
Constraint l < u, u < p.
Context {A X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (r : Ordinal 2).
Context (H K : Ordinal 2 → SimplicialCylinderF A ⇒ X).
Context (EP : cylinder_time_endpoint_matching r H).
Context (EF : cylinder_time_factor_matching r H).

Definition higher_forward
  : cylinder_time_factor_matching r H
  := cylinder_time_factors_from_endpoints r H EP.

Definition higher_backward
  : cylinder_time_endpoint_matching r H
  := cylinder_time_endpoints_from_factors r H EF.

Definition higher_iff
  : cylinder_time_endpoint_matching r H ↔ cylinder_time_factor_matching r H
  := cylinder_time_matching_iff r H.

Definition higher_proper (E : ∀ j, ¬ j = r → H j ≈N K j)
  : cylinder_time_factor_matching r H ↔ cylinder_time_factor_matching r K
  := cylinder_time_factor_matching_proper r H K E.

End higher_sizes.

(** * Actual Initial-Region Consumer

    Endpoint matching discharges the existing all-factor input. The
    nine-step extension still requires its nine explicit choices. *)

(** * 实际初始域消费者

    端点相容满足已有全部共同因子输入；九步延拓仍须显式给出九份选择。 *)

Section InitialRegion.
Universes l u p.
Constraint l < u, u < p.
Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.
Context (r : Ordinal 2).
Context (B : SimplicialParameterF (∂Δ[2]) 2 ⇒ X).
Context (H : Ordinal 2 → SimplicialCylinderF (Δ[2]) ⇒ X).
Context (EB : triangle_input_boundary_agreement r B H).
Context (EP : cylinder_time_endpoint_matching r H).

Definition actual_factor_input
  : triangle_input_face_agreement r H
  := cylinder_time_factors_from_endpoints r H EP.

Definition actual_initial_map
  : TriangleHornStage r 0 ⇒ X
  := TriangleInputN r B H EB actual_factor_input.

Definition actual_initial_face j (Hj : ¬ j = r) n z
  : actual_initial_map n
      (triangle_input_generator r (inr (j; (Hj, (n; z))))) ≈S H j n z
  := triangle_input_face_β r B H EB actual_factor_input j Hj n z.

Definition actual_nine_step_extension
    (C : ∀ s, HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s))
  : ∃ T : (TriangleHornAmbient : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ X,
      (T ∘Nv RegionInclusionN (TriangleHornRegion r 0)) ≈N actual_initial_map
  := TriangleHornProductExtension r C actual_initial_map.

End InitialRegion.
