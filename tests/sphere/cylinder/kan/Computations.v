From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderKan
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Nine-Step Choices Give Actual Cylinder Maps

    Native-distinct values have Boolean equality witnesses. Explicit
    constant fillers let the whole nine-step construction compute while
    keeping native choice data visible. No choice equations are assumed. *)

(** * 实际九步选择给出实际柱映射

    原生不同取值具有布尔相等见证。显式常值填充使整个九步构造可计算，并保留
    原生选择数据的差异；不假定选择之间有方程。 *)

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

Program Definition actual_homotopy (a b : TwoSphereS W false) (q : nat)
  : SimplicialHomotopy (@simplex_map_resp W 2 a.1)
      (@simplex_map_resp W 2 b.1)
  :=
  {|homotopy_map := actual_map q
  |}.
Next Obligation. intros n z. exact true. Defined.

Definition H
  : TwoSphereCylinderHomotopy W false x y
  := (actual_homotopy x y 0; λ n a t, false).

Definition L
  : TwoSphereCylinderHomotopy W false y x
  := (actual_homotopy y x 1; λ n a t, true).

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

Definition reverse_triangle (v : bool)
  := SphereRelativeTriangleExtension W false fin_first (choices fin_first v)
      (SphereReverseEdges W false H) (sphere_reverse_edges_relative W false H)
      (sphere_reverse_edges_endpoints W false H).

Definition reversed (v : bool)
  := SphereCylinderReverse W false (choices fin_first v) H.

Definition composite (v : bool)
  := SphereCylinderComposite W false (choices fin_first⁺ v) H L.

Definition parameter_time
  : (Δ[1]) 2
  := {|lower := σ[1; fin_first]|}.

Example actual_missing_edges_compute
  : (homotopy_map (reversed false).1 2 (simplex_generic 2, parameter_time),
     homotopy_map (reversed true).1 2 (simplex_generic 2, parameter_time),
     homotopy_map (composite false).1 2 (simplex_generic 2, parameter_time),
     homotopy_map (composite true).1 2 (simplex_generic 2, parameter_time))
      = (false, true, false, true).
Proof. vm_compute. reflexivity. Defined.

Example selected_triangle_boundary_values_compute
  : ((reverse_triangle false).1 2
        ({|lower := δ[1; fin_first] ∘ σ[1; fin_first]|}, simplex_generic 2),
     (reverse_triangle true).1 2
        ({|lower := δ[1; fin_first] ∘ σ[1; fin_first]|}, simplex_generic 2))
      = (false, true).
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

Definition actual_full_reverse_boundary (v : bool)
  : homotopy_map (reversed v).1 5 (ι∂[2] 5 boundary_space, varying_time) ≈S
      simplex_constant W false 5
  := (reversed v).2 5 boundary_space varying_time.

Definition actual_full_composite_boundary (v : bool)
  : homotopy_map (composite v).1 5 (ι∂[2] 5 boundary_space, varying_time) ≈S
      simplex_constant W false 5
  := (composite v).2 5 boundary_space varying_time.

Example fifth_degree_output_values_compute
  : (homotopy_map (reversed false).1 5
       (ι∂[2] 5 boundary_space, varying_time),
     homotopy_map (reversed true).1 5
       (ι∂[2] 5 boundary_space, varying_time)) = (false, true).
Proof. vm_compute. reflexivity. Defined.

Definition full_retained_recovery (v : bool)
  : simplicial_triangle_edge (reverse_triangle v).1 fin_first⁺⁺ ≈N
      homotopy_map H.1
  := snd (reverse_triangle v).2 fin_first⁺⁺ (ltac:(discriminate)).

Example the_same_selected_triangle_supplies_the_output (v : bool)
  : homotopy_map (reversed v).1 =
      simplicial_triangle_edge (reverse_triangle v).1 fin_first
  := eq_refl.

Fail Definition choice_outputs_are_native_equal
  : homotopy_map (reversed false).1 2 (simplex_generic 2, parameter_time) =
      homotopy_map (reversed true).1 2 (simplex_generic 2, parameter_time)
  := ltac:(vm_compute; reflexivity).

Fail Definition boundary_recovery_is_native
  : homotopy_map (reversed true).1 5
      (ι∂[2] 5 boundary_space, varying_time) = simplex_constant W false 5
  := ltac:(vm_compute; reflexivity).

Fail Definition choices_do_not_select_full_Kan
  : HasKanFillers W
  := ltac:(typeclasses eauto).

Fail Definition no_automatic_directed_equivalence
  : Equivalence (TwoSphereCylinderHomotopy W false)
  := ltac:(typeclasses eauto).

(** ** An Actual Nonzero Kan Consumer

    Consume the explicit cocycle choices themselves. Specialize endpoint
    recovery only after checking it for an abstract map, avoiding expansion
    of the whole nine-step term during type checking. *)

(** ** 实际非零Kan消费者

    消费显式cocycle选择本身。先对抽象映射检查端点恢复，再作特化，避免类型检查
    展开整个九步项。 *)

Local Opaque SphereRelativeTriangleExtension SphereCylinderReverse
  SphereCylinderComposite.

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

Definition actual_nonzero_reverse
  : TwoSphereCylinderHomotopy Z b Sph Sph
  := SphereCylinderReverse Z b (cocycle_choices fin_first) original.

Definition actual_nonzero_composite
  : TwoSphereCylinderHomotopy Z b Sph Sph
  := SphereCylinderComposite Z b (cocycle_choices fin_first⁺) original original.

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

Definition actual_nonzero_reverse_endpoint
  := nonzero_endpoint_from (homotopy_map actual_nonzero_reverse.1)
      (simplicial_homotopy_0 actual_nonzero_reverse.1).

Definition actual_nonzero_composite_endpoint
  := nonzero_endpoint_from (homotopy_map actual_nonzero_composite.1)
      (simplicial_homotopy_0 actual_nonzero_composite.1).

Definition actual_nonzero_reverse_boundary
  := actual_nonzero_reverse.2 5 boundary_space varying_time.

Definition actual_nonzero_composite_boundary
  := actual_nonzero_composite.2 5 boundary_space varying_time.

Local Transparent SphereRelativeTriangleExtension SphereCylinderReverse
  SphereCylinderComposite.
