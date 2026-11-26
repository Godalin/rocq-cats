From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderBase
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Native-Distinct Vertices and Independent Witnesses

    In the constant witness setoid, false and true are equal by either
    boolean witness. Base transport keeps triangles. Independently chosen
    source/target group products and inverses can have native-distinct
    outputs; the new laws must still provide actual relative cylinders. *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation. split; red; intros; exact true. Defined.

(** Retain the witness setoid in every degree. *)

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

(** The original input retains its boundary witnesses. *)

Definition x
  : TwoSphereS W false
  := (false; λ i, true).

(** A second native-distinct input has different witnesses. *)

Definition y
  : TwoSphereS W false
  := (true; λ i, false).

(** Constant prescribed fillers are genuine choices, not unique or Proper. *)

Program Definition one_choice (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers W n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m z. exact true. Defined.

(** Independent presentation families need not be carried to each other. *)

Definition choices (r : Ordinal 2) (v : bool) (s : Ordinal 8)
  : HasHornFillers W (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s)
  := one_choice _ _ v.

(** Supply only the four-dimensional choices used by the actual groups. *)

Local Definition four2
  : HasHornFillers W 4 fin_first⁺⁺
  := one_choice _ _ false.

(** Associativity retains its own choice. *)

Local Definition four3
  : HasHornFillers W 4 fin_first⁺⁺⁺
  := one_choice _ _ true.

(** Input descent retains its other choice. *)

Local Definition four4
  : HasHornFillers W 4 fin_first⁺⁺⁺⁺
  := one_choice _ _ false.

Local Existing Instance four2.
Local Existing Instance four3.
Local Existing Instance four4.

(** The basepoint and the presentation choices are independent parameters. *)

Definition Q (b r c : bool)
  : SetC
  := TwoSphereCylinderS W b (choices fin_first r) (choices fin_first⁺ c).

(** Product and left candidate use the supplied value; the right candidate
    is independently false. No chosen model is registered. *)

Definition G (b r c v : bool)
  : Group
  := TwoSphereCylinderGroup W b (choices fin_first r) (choices fin_first⁺ c)
      (one_choice _ _ v) (one_choice _ _ v) (one_choice _ _ false).

(** Transport changes the vertex and the presentation, not the triangle. *)

Definition moved (E : @carrier_equiv WitnessS false true)
  : Q false false true →r Q true true false
  := two_sphere_cylinder_change_base_resp W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) E.

(** The actual source and target groups retain different selections. *)

Definition product_cylinder
  : TwoSphereCylinderHomotopy W true
      (moved true (@mul _ (hasMagma (G false false true false)) x y))
      (@mul _ (hasMagma (G true true false true)) (moved true x) (moved true y))
  := two_sphere_cylinder_change_base_mul W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) true
      (one_choice _ _ false) (one_choice _ _ true) x y.

(** Left inverse preservation uses those same selected group operations. *)

Definition inverse_cylinder
  : TwoSphereCylinderHomotopy W true
      (moved false (@inv _ _ _ (hasInverse (G false false true false)) x))
      (@inv _ _ _ (hasInverse (G true true false true)) (moved false x))
  := two_sphere_cylinder_change_base_left_inverse W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) false
      (one_choice _ _ false) (one_choice _ _ true)
      (one_choice _ _ true) (one_choice _ _ false) x.

(** Units use the native-distinct specified equal vertices. *)

Definition unit_cylinder
  : TwoSphereCylinderHomotopy W true
      (moved true (@mul_unit _ _ (hasUnit (G false false true false))))
      (@mul_unit _ _ (hasUnit (G true true false true)))
  := @two_sphere_cylinder_change_base_unit W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) false true true.

(** Equality witnesses remain different boolean data. *)

Definition witness_cylinder
  := @two_sphere_cylinder_change_base_witness W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) false true true false y.

(** Identity uses its original presentation. *)

Definition identity_cylinder
  := two_sphere_cylinder_change_base_id W
      (choices fin_first false) (choices fin_first⁺ true) false y.

(** Two transports retain an independent intermediate presentation. *)

Definition composition_cylinder
  := @two_sphere_cylinder_change_base_comp W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (choices fin_first false) (choices fin_first⁺ false)
      false true false true false y.

(** Map an actual input cylinder using the new respectful map. *)

Definition mapped_input_cylinder
  := @func_proper _ _ (moved false) x y
      (TwoSphereConstantCylinder W false x y true).

(** The old generic composite isomorphism supplies both directions. *)

Definition comparison
  := @two_sphere_cylinder_change_base_iso W
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) false true true.

(** Evaluate retained triangles and the actual distinct endpoints of product/inverse/unit preservation. *)

Example transport_and_operations_compute
  : ((moved true y).1, (moved false y).1,
     (moved true (@mul _ (hasMagma (G false false true false)) x y)).1,
     (@mul _ (hasMagma (G true true false true)) (moved true x) (moved true y)).1,
     (moved false (@inv _ _ _ (hasInverse (G false false true false)) x)).1,
     (@inv _ _ _ (hasInverse (G true true false true)) (moved false x)).1,
     (moved true (@mul_unit _ _ (hasUnit (G false false true false)))).1,
     (@mul_unit _ _ (hasUnit (G true true false true))).1) =
    (true, true, false, true, false, true, false, true).
Proof. vm_compute. reflexivity. Defined.

(** Both directions use precisely the raw base-change representative. *)

Example comparison_directions_compute
  : ((lower (comparison.1 {|lower := x|})).1,
     (lower (comparison.2.1 {|lower := moved false y|})).1) = (false, true).
Proof. vm_compute. reflexivity. Defined.

Definition forward_is_same_map (a : Q false false true)
  : lower (comparison.1 {|lower := a|}) = moved true a
  := eq_refl.

Definition backward_is_same_map (a : Q true true false)
  : lower (comparison.2.1 {|lower := a|}) =
      two_sphere_change_base_resp W (symmetry (true :
        @carrier_equiv WitnessS false true)) a
  := eq_refl.

(** A boundary shape is independent of its varying time coordinate. *)

Definition boundary_space
  : (∂Δ[2]) 5
  := {|lower := (δ[1; fin_first⁺] ∘
        SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4);
      sieve_precomp (BoundarySieve 2) δ[1; fin_first⁺]
        (SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4))
        (boundary_face_member fin_first⁺))|}.

(** Time varies through a separate simplex operator. *)

Definition varying_time
  : (Δ[1]) 5
  := {|lower := SimplexPrismTimeF (fin_first⁺ : Ordinal 4)|}.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Every new pointwise law retains the complete relative boundary. *)

Definition all_seven_full_boundaries
  := (product_cylinder.2 5 boundary_space varying_time,
      inverse_cylinder.2 5 boundary_space varying_time,
      unit_cylinder.2 5 boundary_space varying_time,
      witness_cylinder.2 5 boundary_space varying_time,
      identity_cylinder.2 5 boundary_space varying_time,
      composition_cylinder.2 5 boundary_space varying_time,
      mapped_input_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Actual-cylinder equations do not imply native endpoint equality. *)

Fail Definition product_not_native
  : moved true (@mul _ (hasMagma (G false false true false)) x y) =
      @mul _ (hasMagma (G true true false true)) (moved true x) (moved true y)
  := ltac:(vm_compute; reflexivity).
Fail Definition inverse_not_native
  : moved false (@inv _ _ _ (hasInverse (G false false true false)) x) =
      @inv _ _ _ (hasInverse (G true true false true)) (moved false x)
  := ltac:(vm_compute; reflexivity).
Fail Definition unit_not_native
  : moved true (@mul_unit _ _ (hasUnit (G false false true false))) =
      @mul_unit _ _ (hasUnit (G true true false true))
  := ltac:(vm_compute; reflexivity).

(** ** The Actual Nonzero Cocycle Sphere

    Reuse the real Kan choices and coefficient decoder. Reflexive base
    transport still consumes the new construction, preserves the nonzero
    sphere and supplies actual cylinders for the same group operations. *)

Local Existing Instance BoolCocycleModel_HasKanFillers.

Definition Z
  : Fct (Δ^op) SetCat
  := BoolCocycleModel.

(** Keep the original unit basepoint. *)

Definition b
  : Z 0
  := (two_cocycle_simplex_unit (M := BoolS_Monoid)) 0.

(** Select the actual model's presentation fillers explicitly. *)

Definition cocycle_choices (r : Ordinal 2) (s : Ordinal 8)
  := @hasHornFillers Z BoolCocycleModel_HasKanFillers
      (simplex_triangle_horn_face_dim s) (simplex_triangle_horn_missing r s).

(** The target equality remains actual full relative cylinders. *)

Definition CZ
  : SetC
  := TwoSphereCylinderS Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺).

(** Supply the actual product choice. *)

Definition product_choice
  : HasHornFillers Z 3 fin_first⁺⁺
  := _.

(** Supply the actual left-candidate choice separately. *)

Definition left_choice
  : HasHornFillers Z 3 fin_first⁺⁺⁺
  := _.

(** The right choice remains a separate argument. *)

Definition right_choice
  : HasHornFillers Z 3 fin_first⁺
  := _.

(** Choose the exact same original cylinder group. *)

Definition GZ
  : Group
  := TwoSphereCylinderGroup Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺) product_choice left_choice right_choice.

(** Reflexive transport uses the new cylinder base map. *)

Definition model_mapped
  : CZ →r CZ
  := two_sphere_cylinder_change_base_resp Z
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺) (reflexivity b).

(** Decode through the original class comparison, retaining the new map's
    actual output rather than replacing its selected operation. *)

Definition value
  : CZ →r BoolS
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) ∘r
      two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
        (cocycle_choices fin_first⁺).

(** Nonzero transport and its inverse have the expected coefficients. *)

Example nonzero_transport_compute
  : (value (model_mapped bool_cocycle_sphere),
     value (model_mapped (@inv _ _ _ (hasInverse GZ) bool_cocycle_sphere)),
     value (@inv _ _ _ (hasInverse GZ) (model_mapped bool_cocycle_sphere))) =
    (true, true, true).
Proof. vm_compute. reflexivity. Defined.

(** The new inverse law is an actual cocycle cylinder. *)

Definition cocycle_inverse_cylinder
  := two_sphere_cylinder_change_base_left_inverse Z
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (reflexivity b) left_choice product_choice left_choice right_choice
      bool_cocycle_sphere.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

Definition cocycle_full_boundary
  := cocycle_inverse_cylinder.2 5 boundary_space varying_time.

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** The transported actual nonzero sphere is still not the unit. *)

Definition transported_nonzero_not_unit
  : ¬ ((model_mapped bool_cocycle_sphere : CZ) ≈S @mul_unit _ _ (hasUnit GZ)).
Proof.
  intros E. pose proof (@func_proper CZ BoolS value _ _ E) as H.
  change (true = false) in H. discriminate H.
Defined.

(** Full Kan still does not enable a group or raw cylinder equivalence. *)

Fail Definition full_Kan_no_group : HasMagma CZ := ltac:(typeclasses eauto).
Fail Definition full_Kan_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Z b)
  := ltac:(typeclasses eauto).
