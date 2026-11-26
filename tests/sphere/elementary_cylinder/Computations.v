From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereElementaryCylinder
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Direction and Actual Data Without Kan Choices

    Use a constant simplicial setoid with Boolean equality witnesses.
    The endpoint triangles, tetrahedra and law witnesses may be native
    distinct. No native equality of those representatives is assumed. *)

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

Definition elementary
  : TwoSphereHomotopy W false x y
  := (true; (false, (true, (false, true)))).

Definition cylinder
  : TwoSphereCylinderHomotopy W false y x
  := TwoSphereHomotopyCylinder W false elementary.

Definition K
  := homotopy_map cylinder.1.

Example actual_pieces_and_reversed_endpoints
  : (simplex_prism_eval K fin_first, simplex_prism_eval K fin_first⁺,
     simplex_prism_eval K fin_first⁺⁺,
     simplex_element_resp (K ∘Nv SimplicialEndpointN (Δ[2]) false),
     simplex_element_resp (K ∘Nv SimplicialEndpointN (Δ[2]) true)) =
      (false, false, true, true, false).
Proof. vm_compute. reflexivity. Defined.

Definition native_faces (w : W 3)
  : bool * bool * bool * bool
  := (d[W; 2; fin_first] w, d[W; 2; fin_first⁺] w,
      d[W; 2; fin_first⁺⁺] w, d[W; 2; fin_first⁺⁺⁺] w).

(** Specified side equations do not force native-constant side values. *)

Example native_face_values_keep_the_tetrahedron
  : (native_faces (simplex_prism_eval K fin_first),
     native_faces (simplex_prism_eval K fin_first⁺),
     native_faces (simplex_prism_eval K fin_first⁺⁺)) =
      ((false, false, false, false), (false, false, false, false),
       (true, true, true, true)).
Proof. vm_compute. reflexivity. Defined.

Definition independent_laws
  : TwoSphereHomotopy W false x y
  := (true; (true, (false, (true, false)))).

Definition independent_laws_same_map
  : K ≈N homotopy_map (TwoSphereHomotopyCylinder W false independent_laws).1
  := two_sphere_homotopy_cylinder_map_proper W false
      elementary independent_laws true false.

Definition different_representatives
  : TwoSphereHomotopy W false y x
  := (false; (true, (false, (true, false)))).

Definition different_representatives_equal_map
  : K ≈N homotopy_map
      (TwoSphereHomotopyCylinder W false different_representatives).1
  := two_sphere_homotopy_cylinder_map_proper W false
      elementary different_representatives false true.

Example native_distinct_tetrahedra_are_retained
  : (simplex_prism_eval K fin_first⁺⁺,
     simplex_prism_eval (homotopy_map
       (TwoSphereHomotopyCylinder W false different_representatives).1)
       fin_first⁺⁺) = (true, false).
Proof. vm_compute. reflexivity. Defined.

Fail Definition specified_tetrahedra_are_native_equal
  : elementary.1 = different_representatives.1
  := eq_refl.

(** Inspect the full relative law at an actual degree-five boundary
    datum and a separately varying time operator. *)

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

Definition original_tetrahedron_recovered
  : simplex_prism_eval K fin_first⁺⁺ ≈S elementary.1
  := two_sphere_homotopy_cylinder_prism W false elementary fin_first⁺⁺.

Fail Definition unchosen_Kan
  : HasKanFillers W
  := _.

Fail Definition unchosen_horn
  : HasHornFillers W 3 fin_first⁺⁺
  := _.

Fail Definition unproved_cylinder_equivalence
  : Equivalence (TwoSphereCylinderHomotopy W false)
  := _.

(** ** A Genuine Nonzero Cocycle Tetrahedron

    Supply the existing elementary cocycle witness itself. The new
    constructor uses its data, without the specialized coefficient
    cylinder theorem or a selected Kan structure. *)


Definition coefficient_elementary
  : TwoSphereHomotopy BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      bool_cocycle_sphere bool_cocycle_sphere
  := CocycleTwoSphereHomotopy bool_cocycle_sphere bool_cocycle_sphere eq_refl.

Definition coefficient_cylinder
  := TwoSphereHomotopyCylinder BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      coefficient_elementary.

Definition coefficient_map
  := homotopy_map coefficient_cylinder.1.

Definition coefficient_faces (i : Ordinal 2)
  : bool * bool * bool * bool
  := let w := simplex_prism_eval coefficient_map i in
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid) (d[BoolCocycleModel; 2; fin_first] w),
       (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺] w),
       (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
       (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example twelve_actual_cocycle_face_coefficients
  : (coefficient_faces fin_first, coefficient_faces fin_first⁺,
     coefficient_faces fin_first⁺⁺) =
      ((true, true, false, false), (false, true, true, false),
       (false, false, true, true)).
Proof. vm_compute. reflexivity. Defined.

Example cocycle_endpoints_keep_the_nonzero_label
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid) (simplex_element_resp
       (coefficient_map ∘Nv SimplicialEndpointN (Δ[2]) false)),
     (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (simplex_element_resp
       (coefficient_map ∘Nv SimplicialEndpointN (Δ[2]) true))) = (true, true).
Proof. vm_compute. reflexivity. Defined.
