From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SpherePrismRelative
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Relative Reconstruction with Distinct Native Data

    Equality witnesses below are Boolean data. Native-distinct values
    can therefore obey the six side equations without being literally
    the base value. No filling or algebra structure is chosen. *)

Definition side_ranks (j : Ordinal 2) (k : Ordinal 1)
  : nat * nat
  := (fin_rank (fst (simplex_triangle_prism_side j k)),
      fin_rank (snd (simplex_triangle_prism_side j k))).

Example six_actual_side_positions
  : (side_ranks fin_first fin_first, side_ranks fin_first fin_first⁺,
     side_ranks fin_first⁺ fin_first, side_ranks fin_first⁺ fin_first⁺,
     side_ranks fin_first⁺⁺ fin_first, side_ranks fin_first⁺⁺ fin_first⁺) =
      ((1, 0), (2, 0), (0, 2), (2, 1), (0, 3), (1, 3)).
Proof. vm_compute. reflexivity. Defined.

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

Definition values (i : Ordinal 2)
  : W 3
  := Nat.eqb (fin_rank i) 0.

Definition sides
  : is_two_sphere_prism_relative W false values
  := λ j k, Nat.eqb (fin_rank j) (fin_rank k).

Definition cylinder
  : TwoSphereCylinderHomotopy W false x y
  := SpherePrismCylinder W false values true false x y false true sides.

Definition other_cylinder
  : TwoSphereCylinderHomotopy W false x y
  := SpherePrismCylinder W false values false true x y true false
      (λ j k, false).

Definition K
  : SimplicialCylinderF (Δ[2]) ⇒ W
  := homotopy_map cylinder.1.

Example actual_values_and_endpoints
  : (simplex_prism_eval K fin_first, simplex_prism_eval K fin_first⁺,
     simplex_prism_eval K fin_first⁺⁺,
     simplex_element_resp (K ∘Nv SimplicialEndpointN (Δ[2]) false),
     simplex_element_resp (K ∘Nv SimplicialEndpointN (Δ[2]) true)) =
      (true, false, false, false, true).
Proof. vm_compute. reflexivity. Defined.

Example six_actual_boundary_values
  : (two_sphere_boundary_prism_value W K fin_first fin_first,
     two_sphere_boundary_prism_value W K fin_first fin_first⁺,
     two_sphere_boundary_prism_value W K fin_first⁺ fin_first,
     two_sphere_boundary_prism_value W K fin_first⁺ fin_first⁺,
     two_sphere_boundary_prism_value W K fin_first⁺⁺ fin_first,
     two_sphere_boundary_prism_value W K fin_first⁺⁺ fin_first⁺) =
      (false, false, true, false, true, false).
Proof. vm_compute. reflexivity. Defined.

Definition independent_law_witnesses
  : homotopy_map cylinder.1 ≈N homotopy_map other_cylinder.1
  := simplex_triangle_prism_gluing_proper values values
      true false false true (λ i, true).

Definition roundtrip_map
  : homotopy_map (SpherePrismReconstruct W false cylinder).1 ≈N K
  := two_sphere_prism_reconstruct_map W false cylinder.

Fail Definition boundary_is_native_constant
  : two_sphere_boundary_prism_value W K fin_first⁺ fin_first =
      simplex_constant W false 2
  := eq_refl.

(** A genuine degree-five boundary datum uses a nonconstant time
    coordinate. The same-factor boundary theorem covers it directly. *)

Definition edge_space
  : (@Hom Δ) 5 1%nat
  := SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4).

Definition edge_time
  : (@Hom Δ) 5 1%nat
  := SimplexPrismTimeF (fin_first⁺ : Ordinal 4).

Definition boundary_datum
  : (∂Δ[2]) 5
  := {|lower := (δ[1; fin_first⁺] ∘ edge_space;
      sieve_precomp (BoundarySieve 2) δ[1; fin_first⁺] edge_space
        (boundary_face_member fin_first⁺))|}.

Definition full_time_boundary
  : K 5 (ι∂[2] 5 boundary_datum, {|lower := edge_time|}) ≈S
      simplex_constant W false 5
  := cylinder.2 5 boundary_datum {|lower := edge_time|}.

Example high_degree_boundary_is_native_distinct
  : (K 5 (ι∂[2] 5 boundary_datum, {|lower := edge_time|}),
     simplex_constant W false 5) = (true, false).
Proof. vm_compute. reflexivity. Defined.

(** ** Nonzero Cocycle Cylinder Without a Kan Selection

    Reconstruct an existing constant relative cylinder. Endpoints retain
    their nonzero coefficient while every side coefficient is zero. *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Fail Definition unchosen_horn
  : HasHornFillers BoolCocycleModel 4 fin_first
  := _.


Definition coefficient_native_equal
  : (bool_cocycle_sphere : TwoSphereS BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)) ≈S bool_cocycle_sphere.
Proof. reflexivity. Defined.

Definition coefficient_cylinder
  := TwoSphereConstantCylinder BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      bool_cocycle_sphere bool_cocycle_sphere coefficient_native_equal.

Definition coefficient_reconstructed
  := SpherePrismReconstruct BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      coefficient_cylinder.

Definition coefficient_map
  := homotopy_map coefficient_reconstructed.1.

Definition coefficient_side (j : Ordinal 2) (k : Ordinal 1)
  : bool
  := (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (two_sphere_boundary_prism_value BoolCocycleModel coefficient_map j k).

Example coefficient_endpoints_retained
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid) (simplex_element_resp
       (coefficient_map ∘Nv SimplicialEndpointN (Δ[2]) false)),
     (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (simplex_element_resp
       (coefficient_map ∘Nv SimplicialEndpointN (Δ[2]) true))) = (true, true).
Proof. vm_compute. reflexivity. Defined.

Example coefficient_sides_zero
  : (coefficient_side fin_first fin_first,
     coefficient_side fin_first fin_first⁺,
     coefficient_side fin_first⁺ fin_first,
     coefficient_side fin_first⁺ fin_first⁺,
     coefficient_side fin_first⁺⁺ fin_first,
     coefficient_side fin_first⁺⁺ fin_first⁺) =
      (false, false, false, false, false, false).
Proof. vm_compute. reflexivity. Defined.

Definition coefficient_roundtrip
  : coefficient_map ≈N homotopy_map coefficient_cylinder.1
  := two_sphere_prism_reconstruct_map BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) coefficient_cylinder.

(** ** Boundary Constancy Is a Genuine Additional Condition

    The time projection into the representable interval is an actual
    cylinder map, but is not constant on the boundary. No fixed-endpoint
    claim is made for this counterexample. *)

Definition I
  : Fct (Δ^op) SetCat
  := Δ[1].

Definition base_vertex
  : I 0
  := {|lower := ConstF [Ord 0] (C := [Ord 1]) fin_first|}.

Program Definition time_projection
  : SimplicialCylinderF (Δ[2]) ⇒ I
  :=
  {|nt n := {|func z := snd z|}
  |}.
Next Obligation. intros [a t] [a' t'] [E F]. exact F. Defined.
Next Obligation. reflexivity. Defined.

Example time_projection_not_relative
  : ¬ is_two_sphere_cylinder_relative I base_vertex time_projection.
Proof.
  intros R.
  pose (E := fst (two_sphere_cylinder_relative_iff I base_vertex
    time_projection) R fin_first fin_first).
  pose (F := fst (simplex_eq_iff _ _) (lower E) fin_first⁺⁺).
  discriminate F.
Defined.
