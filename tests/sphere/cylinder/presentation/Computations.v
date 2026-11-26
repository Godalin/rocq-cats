From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderSetoid
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Same Representatives and Actual Equality Witnesses

    Native-distinct triangles and boundary witnesses survive both comparison
    maps and independently enabled cylinder presentations. VM computes the
    values while concrete clients consume actual equality cylinders. *)

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

Definition Q (r k : bool)
  : SetC
  := TwoSphereCylinderS W false (choices fin_first r) (choices fin_first⁺ k).

Definition comparison
  := two_sphere_cylinder_class_iso W false
      (choices fin_first true) (choices fin_first⁺ false).

Definition choice_comparison
  := two_sphere_cylinder_choice_iso W false
      (choices fin_first true) (choices fin_first⁺ false)
      (choices fin_first false) (choices fin_first⁺ true).

Example two_comparison_directions_compute
  : ((lower (comparison.1 {|lower := x|})).1,
     (lower (comparison.2.1 {|lower := y|})).1) = (false, true).
Proof. vm_compute. reflexivity. Defined.

Example enabling_comparison_keeps_boundary_witness_data
  : ((lower (choice_comparison.1 {|lower := y|})).1,
     (lower (choice_comparison.1 {|lower := y|})).2 fin_first) = (true, false).
Proof. vm_compute. reflexivity. Defined.

Definition mapped
  := two_sphere_cylinder_map_resp (IdN : W ⇒ W) false
      (choices fin_first true) (choices fin_first⁺ false)
      (choices fin_first false) (choices fin_first⁺ true).

Example image_representatives_compute
  : ((mapped x).1, (mapped y).1) = (false, true).
Proof. vm_compute. reflexivity. Defined.

Definition elementary
  : TwoSphereHomotopy W false x y
  := (true; (false, (true, (false, true)))).

Definition actual_equality
  : TwoSphereCylinderHomotopy W false x y
  := @func_proper (TwoSphereClassS W false) (Q true false)
      (two_sphere_cylinder_of_class_resp W false
        (choices fin_first true) (choices fin_first⁺ false)) x y
      (two_sphere_class_step W false elementary).

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

Definition actual_equality_full_boundary
  := actual_equality.2 5 boundary_space varying_time.

Fail Definition specified_boundary_is_not_native
  : homotopy_map actual_equality.1 5
      (ι∂[2] 5 boundary_space, varying_time) = simplex_constant W false 5
  := ltac:(vm_compute; reflexivity).

Definition natural_witness
  := two_sphere_cylinder_map_natural (IdN : W ⇒ W) false
      (choices fin_first true) (choices fin_first⁺ false)
      (choices fin_first false) (choices fin_first⁺ true) y.

Definition naturality_full_boundary
  := natural_witness.2 5 boundary_space varying_time.

Definition representative_round_trip_is_native (a : TwoSphereS W false)
  : lower (comparison.2.1 (comparison.1 {|lower := a|})) = a
  := eq_refl.

(** ** The Existing Coefficient Classifier as an Actual Client

    Compose the generic presentation comparison with the existing Boolean
    coefficient isomorphism. This classifies this model's cylinder equality;
    no general π₂ or weak-equivalence identification follows. *)

Local Opaque two_sphere_cylinder_class_iso cocycle_two_sphere_class_iso.

Definition Z
  : Fct (Δ^op) SetCat
  := BoolCocycleModel.

Definition b
  : Z 0
  := (two_cocycle_simplex_unit (M := BoolS_Monoid)) 0.

Definition cocycle_choices (r : Ordinal 2) (s : Ordinal 8)
  := @hasHornFillers Z BoolCocycleModel_HasKanFillers
      (simplex_triangle_horn_face_dim s) (simplex_triangle_horn_missing r s).

Definition geometric_bool_iso
  : LiftS (TwoSphereCylinderS Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺)) ≅[SetCat] LiftS BoolS
  := iso_trans
      (iso_symm (two_sphere_cylinder_class_iso Z b
        (cocycle_choices fin_first) (cocycle_choices fin_first⁺)))
      (@cocycle_two_sphere_class_iso BoolS_Monoid).

Local Transparent two_sphere_cylinder_class_iso cocycle_two_sphere_class_iso.

Example actual_geometric_classifier_computes
  : (lower (geometric_bool_iso.1 {|lower := bool_cocycle_sphere|}),
     (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
       (lower (geometric_bool_iso.2.1 {|lower := false|})).1) = (true, false).
Proof. vm_compute. reflexivity. Defined.

Definition geometric_nonzero_not_null
  : ¬ ((bool_cocycle_sphere : TwoSphereCylinderS Z b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)) ≈S
      two_sphere_base Z b).
Proof.
  intros H. apply bool_cocycle_sphere_not_null.
  exact (@func_proper _ _
    (two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺)) _ _ H).
Defined.

(** ** Full Kan Does Not Choose the New Presentation's Algebra

    Explicitly enable the easy Boolean-witness Kan model only in this
    section; import must still not select a group or raw equivalence. *)

Section ExplicitKan.

Local Program Instance witness_Kan
  : HasKanFillers W
  :=
  {|hasHornFillers n i := one_choice (S n) i false
  |}.

Fail Definition no_automatic_cylinder_group
  : HasMagma (Q true false)
  := ltac:(typeclasses eauto).

Fail Definition no_automatic_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy W false)
  := ltac:(typeclasses eauto).

End ExplicitKan.
