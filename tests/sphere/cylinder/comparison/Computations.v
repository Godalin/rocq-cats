From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderComparison
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Folding Actual Generated Chains

    Native-distinct Boolean representatives retain independent Boolean
    equality/boundary witnesses. Test every closure constructor and compute
    the actual resulting map, without identifying any witness records. *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation. split; red; intros; exact true. Defined.

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Definition x
  : TwoSphereS W false
  := (false; λ i, true).

Definition y
  : TwoSphereS W false
  := (true; λ i, false).

Program Definition one_choice (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers W n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m h'. exact true. Defined.

Definition choices (r : Ordinal 2) (v : bool) (s : Ordinal 8)
  : HasHornFillers W (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s)
  := one_choice _ _ v.

Definition elementary
  : TwoSphereHomotopy W false x y
  := (true; (false, (true, (false, true)))).

Definition mixed_chain
  : (x : TwoSphereClassS W false) ≈S y
  := closure_trans (two_sphere_class_eq W false (x := x) (y := y) false)
      (closure_trans (closure_sym (two_sphere_class_step W false elementary))
        (closure_trans (closure_refl x)
          (two_sphere_class_step W false elementary))).

Definition folded {a c : TwoSphereS W false} (r k : bool)
    (E : (a : TwoSphereClassS W false) ≈S c)
  : TwoSphereCylinderHomotopy W false a c
  := TwoSphereClassCylinder W false (choices fin_first r)
      (choices fin_first⁺ k) E.

Definition parameter_time
  : (Δ[1]) 2
  := {|lower := σ[1; fin_first]|}.

Example constant_cases_compute
  : (homotopy_map (folded true true (closure_refl x)).1 2
       (simplex_generic 2, parameter_time),
     homotopy_map (folded true true
       (two_sphere_class_eq W false (x := x) (y := y) false)).1 2
       (simplex_generic 2, parameter_time)) = (false, false).
Proof. vm_compute. reflexivity. Defined.

Example elementary_direction_is_corrected_and_computes
  : (homotopy_map (folded false true
       (two_sphere_class_step W false elementary)).1 2
       (simplex_generic 2, parameter_time),
     homotopy_map (folded true false
       (two_sphere_class_step W false elementary)).1 2
       (simplex_generic 2, parameter_time)) = (false, true).
Proof. vm_compute. reflexivity. Defined.

Example composite_chain_uses_the_composition_choices
  : (homotopy_map (folded false true mixed_chain).1 2
       (simplex_generic 2, parameter_time),
     homotopy_map (folded true false mixed_chain).1 2
       (simplex_generic 2, parameter_time)) = (true, false).
Proof. vm_compute. reflexivity. Defined.

Definition boundary_space
  : (∂Δ[2]) 5
  := {|lower := (δ[1; fin_first⁺] ∘
        SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4);
      sieve_precomp (BoundarySieve 2) δ[1; fin_first⁺]
        (SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4))
        (boundary_face_member fin_first⁺))|}.

Definition varying_time
  : (Δ[1]) 5
  := {|lower := SimplexPrismTimeF (fin_first⁺ : Ordinal 4)|}.

Definition mixed_chain_full_boundary
  : homotopy_map (folded false true mixed_chain).1 5
      (ι∂[2] 5 boundary_space, varying_time) ≈S simplex_constant W false 5
  := (folded false true mixed_chain).2 5 boundary_space varying_time.

Definition original_endpoints_are_retained
  : (homotopy_map (folded false true mixed_chain).1 ∘Nv
      SimplicialEndpointN (Δ[2]) true) ≈N (@simplex_map_resp W 2 y.1)
  := simplicial_homotopy_1 (folded false true mixed_chain).1.

Fail Definition class_equality_is_not_native_endpoint_equality
  : x.1 = y.1
  := ltac:(reflexivity).

Fail Definition computed_recovery_is_not_native
  : homotopy_map (folded false true mixed_chain).1 5
      (ι∂[2] 5 boundary_space, varying_time) = simplex_constant W false 5
  := ltac:(vm_compute; reflexivity).

(** ** A Real Nonzero Cocycle Chain

    The old forward descent produces its actual three-step derivation.
    Fold that very chain back, using explicitly supplied Kan choices. *)

Local Opaque TwoSphereClassCylinder two_sphere_cylinder_class
  two_sphere_cylinder_class_iff.

Definition Z
  : Fct (Δ^op) SetCat
  := BoolCocycleModel.

Definition b
  : Z 0
  := (two_cocycle_simplex_unit (M := BoolS_Monoid)) 0.

Definition Sph
  : TwoSphereS Z b
  := bool_cocycle_sphere.

Definition original
  := TwoSphereConstantCylinder Z b Sph Sph (ltac:(reflexivity)).

Definition cocycle_choices (r : Ordinal 2) (s : Ordinal 8)
  := @hasHornFillers Z BoolCocycleModel_HasKanFillers
      (simplex_triangle_horn_face_dim s) (simplex_triangle_horn_missing r s).

Definition real_chain
  : (Sph : TwoSphereClassS Z b) ≈S Sph
  := @two_sphere_cylinder_class Z b
      (@hasHornFillers Z BoolCocycleModel_HasKanFillers 3 fin_first⁺)
      (@hasHornFillers Z BoolCocycleModel_HasKanFillers 3 fin_first⁺⁺)
      Sph Sph original.

Definition real_fold
  : TwoSphereCylinderHomotopy Z b Sph Sph
  := TwoSphereClassCylinder Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺) real_chain.

Definition real_fold_boundary
  := real_fold.2 5 boundary_space varying_time.

Definition nonzero_endpoint_from (M : SimplicialCylinderF (Δ[2]) ⇒ Z)
    (E : (M ∘Nv SimplicialEndpointN (Δ[2]) false) ≈N
      (@simplex_map_resp Z 2 Sph.1))
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (simplex_element_resp (M ∘Nv SimplicialEndpointN (Δ[2]) false)) = true.
Proof.
  transitivity (two_cocycle_triangle_value_resp (M := BoolS_Monoid)
    ((@simplex_map_resp Z 2 Sph.1) 2 (simplex_generic 2))).
  - exact (@func_proper (Z 2) BoolS
      (@two_cocycle_triangle_value_resp BoolS_Monoid) _ _
      (E 2 (simplex_generic 2))).
  - reflexivity.
Defined.

Definition real_fold_retains_nonzero_endpoint
  := nonzero_endpoint_from (homotopy_map real_fold.1)
      (simplicial_homotopy_0 real_fold.1).

Definition real_two_way_comparison
  := @two_sphere_cylinder_class_iff Z b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺) Sph Sph.

Definition real_recovered_class
  := fst real_two_way_comparison real_fold.

Local Transparent TwoSphereClassCylinder two_sphere_cylinder_class
  two_sphere_cylinder_class_iff.
