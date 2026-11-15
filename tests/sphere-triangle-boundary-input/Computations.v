From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereTriangleInput
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.
Local Open Scope hom_scope.

(** * Actual Cylinders with Native-Distinct Endpoints and Laws

    Boolean witnesses relate all values, without making them natively
    equal. Maps may vary with time; no Kan selection is supplied. *)

(** * 带原生不同端点与定律的实际柱

    布尔见证关联全部取值，但不使它们原生相等；映射可随时间变化，不给定Kan选择。 *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation.
  split.
  - intros x. exact true.
  - intros x y E. exact E.
  - intros x y z E F. exact E.
Defined.

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Definition x
  : TwoSphereS W false
  := (false; λ i, true).

Definition y
  : TwoSphereS W false
  := (true; λ i, false).

Definition sample_position (n : nat)
  : Ordinal n
  := match n with O => fin_first | S k => fin_first⁺ end.

Program Definition actual_map (q : nat)
  : SimplicialCylinderF (Δ[2]) ⇒ W
  :=
  {|nt n := {|func z := Nat.eqb
      (fin_rank (lower (snd z) (sample_position n))) q|}
  |}.
Next Obligation. intros a a' E. exact true. Defined.
Next Obligation. intros a. exact false. Defined.

Program Definition actual_homotopy (a b : TwoSphereS W false)
    (q : nat) (v : bool)
  : SimplicialHomotopy (@simplex_map_resp W 2 a.1)
      (@simplex_map_resp W 2 b.1)
  :=
  {|homotopy_map := actual_map q
  |}.
Next Obligation. intros n z. exact v. Defined.

Definition actual_cylinder (a b : TwoSphereS W false) (q : nat) (v : bool)
  : TwoSphereCylinderHomotopy W false a b
  := (actual_homotopy a b q v; λ n z t, negb v).

Definition H
  := actual_cylinder x y 0 true.

Definition K
  := actual_cylinder y x 1 false.

Definition composite_input
  := SphereCompositeTriangleInput W false H K.

Definition reverse_input
  := SphereReverseTriangleInput W false H.

Definition parameter_time
  : (Δ[1]) 2
  := {|lower := σ[1; fin_first]|}.

Definition face_point_at (r j : Ordinal 2) (Hj : ¬ j = r)
    (n : nat) (a : (Δ[2]) n) (t : (Δ[1]) n)
  : TriangleHornStage r 0 n
  := triangle_input_generator r (inr (j; (Hj, (n; (a, t))))).

Definition face_point (r j : Ordinal 2) (Hj : ¬ j = r)
  : TriangleHornStage r 0 2
  := face_point_at r j Hj 2 (simplex_generic 2) parameter_time.

Definition boundary_space
  : (∂Δ[2]) 5
  := {|lower := (δ[1; fin_first⁺] ∘
        SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4);
      sieve_precomp (BoundarySieve 2) δ[1; fin_first⁺]
        (SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4))
        (boundary_face_member fin_first⁺))|}.

Definition boundary_parameter
  : (Δ[2]) 5
  := {|lower := δ[1; fin_first] ∘
      SimplexPrismTimeF (fin_first⁺ : Ordinal 4)|}.

Example actual_retained_values
  : (composite_input 2 (face_point fin_first⁺ fin_first (ltac:(discriminate))),
     composite_input 2 (face_point fin_first⁺ fin_first⁺⁺
       (ltac:(discriminate))),
     reverse_input 2 (face_point fin_first fin_first⁺ (ltac:(discriminate))),
     reverse_input 2 (face_point fin_first fin_first⁺⁺ (ltac:(discriminate))))
      = (false, true, false, true).
Proof. vm_compute. reflexivity. Defined.

Example whole_boundary_is_constant
  : (composite_input 5 (triangle_input_generator fin_first⁺
       (inl (5; (boundary_space, boundary_parameter)))),
     reverse_input 5 (triangle_input_generator fin_first
       (inl (5; (boundary_space, boundary_parameter))))) = (false, false).
Proof. vm_compute. reflexivity. Defined.

Example actual_endpoint_values_are_native_distinct
  : (simplex_element_resp
       (homotopy_map H.1 ∘Nv SimplicialEndpointN (Δ[2]) false),
     simplex_element_resp
       (homotopy_map H.1 ∘Nv SimplicialEndpointN (Δ[2]) true),
     x.1, y.1) = (true, false, false, true).
Proof. vm_compute. reflexivity. Defined.

Definition whole_boundary_recovery
  := sphere_triangle_input_boundary_β W false fin_first
      (SphereReverseEdges W false H) (sphere_reverse_edges_relative W false H)
      (sphere_reverse_edges_endpoints W false H)
      5 boundary_space boundary_parameter.

Definition boundary_overlap
  : TriangleHornStage fin_first⁺ 0 5
  := triangle_input_generator fin_first⁺
      (inl (5; (boundary_space,
        {|lower := δ[1; fin_first⁺⁺] ∘
          SimplexPrismTimeF (fin_first⁺ : Ordinal 4)|}))).

Definition retained_overlap
  : TriangleHornStage fin_first⁺ 0 5
  := face_point_at fin_first⁺ fin_first⁺⁺ (ltac:(discriminate)) 5
      (ι∂[2] 5 boundary_space)
      {|lower := SimplexPrismTimeF (fin_first⁺ : Ordinal 4)|}.

Definition actual_overlap_is_equal
  : boundary_overlap ≈S retained_overlap.
Proof. split; refine {|lower := _|}; reflexivity. Defined.

Definition actual_overlap_respectful
  : composite_input 5 boundary_overlap ≈S composite_input 5 retained_overlap
  := @func_proper _ _ (composite_input 5) _ _ actual_overlap_is_equal.

Example specified_overlap_can_keep_native_distinct_values
  : (composite_input 5 boundary_overlap,
     composite_input 5 retained_overlap) = (false, true).
Proof. vm_compute. reflexivity. Defined.

Definition independent_input
  := SphereTriangleInputN W false fin_first (SphereReverseEdges W false H)
      (λ j Hj n a t, true) (λ j k Hj Hk E n a, false).

Definition independent_laws_compare
  : reverse_input ≈N independent_input.
Proof. apply sphere_triangle_input_proper. intros j Hj n z. exact true. Defined.

Definition altered_cylinder
  := actual_cylinder x y 0 false.

Example endpoint_and_relative_laws_do_not_change_native_values
  : SphereReverseTriangleInput W false altered_cylinder 2
      (face_point fin_first fin_first⁺⁺ (ltac:(discriminate))) =
      reverse_input 2
      (face_point fin_first fin_first⁺⁺ (ltac:(discriminate))).
Proof. vm_compute. reflexivity. Defined.

Fail Definition matching_is_native_endpoint_equality
  : simplex_element_resp
      (homotopy_map H.1 ∘Nv SimplicialEndpointN (Δ[2]) true) = y.1
  := ltac:(vm_compute; reflexivity).

Fail Definition no_automatic_Kan
  : HasKanFillers W
  := ltac:(typeclasses eauto).

Fail Definition no_unproved_directed_equivalence
  : Equivalence (TwoSphereCylinderHomotopy W false)
  := ltac:(typeclasses eauto).

Fail Definition no_reverse_from_initial_data
  : TwoSphereCylinderHomotopy W false y x
  := SphereReverseTriangleInput W false H.

(** ** A Genuine Nonzero Sphere is Retained

    Use a time-independent cylinder on the true cocycle sphere. The
    initial map keeps that sphere on the retained time edges and the
    actual basepoint on the whole spatial boundary; no Kan is consumed. *)

(** ** 保留真实非零球面

    使用真系数球面的时间无关柱。初始映射在保留时间边上保持该球面，整个空间
    边界则取实际基点；不消费Kan选择。 *)

Local Existing Instance BoolS_Monoid.

Definition nonzero_cylinder
  := TwoSphereConstantCylinder BoolCocycleModel (two_cocycle_simplex_unit 0)
      bool_cocycle_sphere bool_cocycle_sphere (ltac:(reflexivity)).

Definition nonzero_input
  := SphereReverseTriangleInput BoolCocycleModel (two_cocycle_simplex_unit 0)
      nonzero_cylinder.

Example nonzero_coefficients_are_preserved
  : (two_cocycle_triangle_value_resp
       (nonzero_input 2 (face_point fin_first fin_first⁺
         (ltac:(discriminate)))),
     two_cocycle_triangle_value_resp
       (nonzero_input 2 (face_point fin_first fin_first⁺⁺
         (ltac:(discriminate))))) = (true, true).
Proof. vm_compute. reflexivity. Defined.
