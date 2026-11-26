From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderHomotopy
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Homotopy Inverses and Non-Native Recovery

    Negation and identity have actual time-varying composite homotopies in
    this Type-valued witness setoid. Distinct constant-trajectory witnesses
    are supplied explicitly. The inverse-image base and both round trips
    differ natively, while actual-cylinder recovery remains available.
    Presentation choices alone supply the required homotopy comparisons. *)

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

(** Negation is respectful in every degree. *)

Program Definition flip_resp
  : WitnessS →r WitnessS
  :=
  {|func := negb
  |}.
Next Obligation. intros a c E. exact E. Defined.

(** A constant component is natural for the constant simplicial object. *)

Program Definition FlipN
  : W ⇒ W
  :=
  {|nt n := flip_resp
  |}.
Next Obligation. intros a. exact true. Defined.

(** The actual maps are negation and identity; time variation and the
    two constant-trajectory witnesses are independent supplied data. *)

Program Definition MovingN
  : SimplicialCylinderF W ⇒ W
  :=
  {|nt n :=
      {|func z := if Nat.eqb (fin_rank (lower (snd z) fin_first)) 0
          then negb (fst z) else fst z
      |}
  |}.
Next Obligation. intros z z' E. exact true. Defined.
Next Obligation. intros z. exact false. Defined.

Program Definition left_homotopy
  : SimplicialHomotopy ((IdN : W ⇒ W) ∘Nv FlipN) IdN
  :=
  {|homotopy_map := MovingN
  |}.
Next Obligation. intros n z. exact true. Defined.

Program Definition right_homotopy
  : SimplicialHomotopy (FlipN ∘Nv (IdN : W ⇒ W)) IdN
  :=
  {|homotopy_map := MovingN
  |}.
Next Obligation. intros n z. exact false. Defined.

Definition left_trajectory
  : homotopy_map left_homotopy 1
      (simplex_constant W false 1, simplex_generic 1) ≈S
      simplex_constant W false 1
  := false.

Definition right_trajectory
  : homotopy_map right_homotopy 1
      (simplex_constant W (FlipN 0 false) 1, simplex_generic 1) ≈S
      simplex_constant W (FlipN 0 false) 1
  := true.

(** A sphere at the image vertex has its own boundary witnesses. *)

Definition z
  : TwoSphereS W true
  := (true; λ i, false).

(** Use the original forward map and new corrected inverse. *)

Definition forward
  : Q false false true →r Q true true false
  := two_sphere_cylinder_map_resp FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

Definition backward
  : Q true true false →r Q false false true
  := two_sphere_cylinder_homotopy_inverse_resp FlipN IdN false
      left_homotopy left_trajectory
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

(** The inverse product law uses exactly the selected group parent operations. *)

Definition product_cylinder
  : TwoSphereCylinderHomotopy W false
      (backward (@mul _ (hasMagma (G true true false true)) z z))
      (@mul _ (hasMagma (G false false true false)) (backward z) (backward z))
  := two_sphere_cylinder_homotopy_inverse_mul FlipN IdN false
      left_homotopy left_trajectory
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (one_choice _ _ true) (one_choice _ _ false) z z.

(** Left-candidate preservation consumes the same two inverses. *)

Definition inverse_cylinder
  : TwoSphereCylinderHomotopy W false
      (backward (@inv _ _ _ (hasInverse (G true true false true)) z))
      (@inv _ _ _ (hasInverse (G false false true false)) (backward z))
  := two_sphere_cylinder_homotopy_inverse_left_inverse FlipN IdN false
      left_homotopy left_trajectory
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (one_choice _ _ true) (one_choice _ _ false)
      (one_choice _ _ false) (one_choice _ _ false) z.

(** Unit preservation really corrects true to false. *)

Definition unit_cylinder
  : TwoSphereCylinderHomotopy W false
      (backward (@mul_unit _ _ (hasUnit (G true true false true))))
      (@mul_unit _ _ (hasUnit (G false false true false)))
  := two_sphere_cylinder_homotopy_inverse_unit FlipN IdN false
      left_homotopy left_trajectory
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

(** Both round trips compare the actual original representatives. *)

Definition left_cylinder
  : TwoSphereCylinderHomotopy W false (backward (forward x)) x
  := two_sphere_cylinder_homotopy_inverse_l FlipN IdN false
      left_homotopy left_trajectory
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false) x.

Definition right_cylinder
  : TwoSphereCylinderHomotopy W true (forward (backward z)) z
  := two_sphere_cylinder_homotopy_inverse_r FlipN IdN false
      left_homotopy left_trajectory
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      right_homotopy right_trajectory z.

(** The respectful inverse consumes an actual input cylinder. *)

Definition mapped_input_cylinder
  := @func_proper _ _ backward z (two_sphere_base W true)
      (TwoSphereConstantCylinder W true z (two_sphere_base W true) true).

(** Reflection consumes an actual image cylinder, without a right homotopy. *)

Definition reflected_cylinder
  := two_sphere_cylinder_homotopy_reflect FlipN IdN false
      left_homotopy left_trajectory
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      x (true; λ i, false)
      (TwoSphereConstantCylinder W true (forward x)
        (forward (true; λ i, false)) true).

(** A common-lift isomorphism reuses the original class comparison. *)

Definition comparison
  := two_sphere_cylinder_homotopy_iso FlipN IdN false
      left_homotopy left_trajectory
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      right_homotopy right_trajectory.

(** Read the nontrivial base correction and all native-distinct law endpoints. *)

Example base_and_operations_compute
  : ((IdN : W ⇒ W) 0 (FlipN 0 false), false,
     (backward (forward x)).1, x.1,
     (forward (backward z)).1, z.1,
     (backward (@mul _ (hasMagma (G true true false true)) z z)).1,
     (@mul _ (hasMagma (G false false true false)) (backward z) (backward z)).1,
     (backward (@inv _ _ _ (hasInverse (G true true false true)) z)).1,
     (@inv _ _ _ (hasInverse (G false false true false)) (backward z)).1,
     (backward (@mul_unit _ _ (hasUnit (G true true false true)))).1,
     (@mul_unit _ _ (hasUnit (G false false true false))).1) =
    (true, false, true, false, false, true, true, false,
     true, false, true, false).
Proof. vm_compute. reflexivity. Defined.

(** Evaluate both supplied trajectories in the actual time-varying map. *)

Example trajectory_data_compute
  : (left_trajectory, right_trajectory,
     homotopy_map left_homotopy 1
       (simplex_constant W false 1, simplex_generic 1),
     homotopy_map right_homotopy 1
       (simplex_constant W true 1, simplex_generic 1)) =
    (false, true, true, false).
Proof. vm_compute. reflexivity. Defined.

(** Both isomorphism directions retain the expected representative functions. *)

Example iso_directions_compute
  : ((lower (comparison.1 {|lower := x|})).1,
     (lower (comparison.2.1 {|lower := z|})).1) = (true, true).
Proof. vm_compute. reflexivity. Defined.

Definition forward_is_same_map (a : Q false false true)
  : lower (comparison.1 {|lower := a|}) = forward a
  := eq_refl.

Definition backward_is_same_map (a : Q true true false)
  : lower (comparison.2.1 {|lower := a|}) = backward a
  := eq_refl.

(** The corrected inverse is also definitionally the old class inverse
    on representatives, including its boundary proof rather than just values. *)

Definition backward_is_old_class_map (a : Q true true false)
  : backward a = two_sphere_class_homotopy_inverse_resp FlipN IdN false
      left_homotopy left_trajectory a
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

(** All five law cylinders and input Proper have full varying-time boundaries. *)

Definition all_seven_full_boundaries
  := (product_cylinder.2 5 boundary_space varying_time,
      inverse_cylinder.2 5 boundary_space varying_time,
      unit_cylinder.2 5 boundary_space varying_time,
      left_cylinder.2 5 boundary_space varying_time,
      right_cylinder.2 5 boundary_space varying_time,
      mapped_input_cylinder.2 5 boundary_space varying_time,
      reflected_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Specified inverse equations and operation laws do not imply native ones. *)

Fail Definition left_not_native
  : backward (forward x) = x
  := ltac:(vm_compute; reflexivity).
Fail Definition right_not_native
  : forward (backward z) = z
  := ltac:(vm_compute; reflexivity).
Fail Definition product_not_native
  : backward (@mul _ (hasMagma (G true true false true)) z z) =
      @mul _ (hasMagma (G false false true false)) (backward z) (backward z)
  := ltac:(vm_compute; reflexivity).
Fail Definition inverse_not_native
  : backward (@inv _ _ _ (hasInverse (G true true false true)) z) =
      @inv _ _ _ (hasInverse (G false false true false)) (backward z)
  := ltac:(vm_compute; reflexivity).
Fail Definition unit_not_native
  : backward (@mul_unit _ _ (hasUnit (G true true false true))) =
      @mul_unit _ _ (hasUnit (G false false true false))
  := ltac:(vm_compute; reflexivity).

(** The reflected actual cylinder also has native-distinct source endpoints. *)

Fail Definition reflected_not_native
  : x = (true; λ i, false)
  := ltac:(vm_compute; reflexivity).

(** ** Real Nonzero Cocycle Consumers

    Actual identity homotopies use the actual Kan fillers, selected
    cylinder group and coefficient decoder. This is a model regression,
    without replacing the corrected inverse or its operation witnesses. *)

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

(** Retain an actual constant homotopy and its explicit base trajectory. *)

Program Definition bool_identity_homotopy
  : SimplicialHomotopy
      ((IdN : BoolCocycleModel ⇒ BoolCocycleModel) ∘Nv IdN) IdN
  :=
  {|homotopy_map := homotopy_map
      (SimplicialConstantHomotopy (IdN : BoolCocycleModel ⇒ BoolCocycleModel))
  |}.
Next Obligation.
  match goal with t : bool |- _ => destruct t end;
    intros n z; reflexivity.
Defined.

Definition bool_identity_trajectory
  : homotopy_map bool_identity_homotopy 1
      (simplex_constant BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) 1,
       simplex_generic 1) ≈S
      simplex_constant BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) 1.
Proof. reflexivity. Defined.

(** Use the actual corrected inverse determined by the first homotopy. *)

Definition model_backward
  : CZ →r CZ
  := two_sphere_cylinder_homotopy_inverse_resp (IdN : Z ⇒ Z) IdN b
      bool_identity_homotopy bool_identity_trajectory
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺).

(** Decode through the original class comparison, retaining the new map's
    actual output rather than replacing its selected operation. *)

Definition value
  : CZ →r BoolS
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) ∘r
      two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
        (cocycle_choices fin_first⁺).

(** Coefficients remain those of the actual product and inverse outputs. *)

Example nonzero_inverse_map_compute
  : (value (model_backward bool_cocycle_sphere),
     value (model_backward
       (@mul _ (hasMagma GZ) bool_cocycle_sphere bool_cocycle_sphere)),
     value (@mul _ (hasMagma GZ) (model_backward bool_cocycle_sphere)
       (model_backward bool_cocycle_sphere)),
     value (model_backward (@inv _ _ _ (hasInverse GZ) bool_cocycle_sphere)),
     value (@inv _ _ _ (hasInverse GZ) (model_backward bool_cocycle_sphere))) =
    (true, false, false, true, true).
Proof. vm_compute. reflexivity. Defined.

(** Both operation laws produce actual cylinders in the real Kan model. *)

Definition cocycle_product_cylinder
  := two_sphere_cylinder_homotopy_inverse_mul (IdN : Z ⇒ Z) IdN b
      bool_identity_homotopy bool_identity_trajectory
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      product_choice product_choice bool_cocycle_sphere bool_cocycle_sphere.

Definition cocycle_inverse_cylinder
  := two_sphere_cylinder_homotopy_inverse_left_inverse (IdN : Z ⇒ Z) IdN b
      bool_identity_homotopy bool_identity_trajectory
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      left_choice product_choice left_choice right_choice bool_cocycle_sphere.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

Definition cocycle_full_boundaries
  := (cocycle_product_cylinder.2 5 boundary_space varying_time,
      cocycle_inverse_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** A nonzero actual inverse image still cannot equal the unit by a cylinder. *)

Definition inverse_image_nonzero_not_unit
  : ¬ ((model_backward bool_cocycle_sphere : CZ) ≈S @mul_unit _ _ (hasUnit GZ)).
Proof.
  intros E. pose proof (@func_proper CZ BoolS value _ _ E) as H.
  change (true = false) in H. discriminate H.
Defined.

(** Reflection rules out an actual image cylinder to the image of the unit,
    consuming only the first real identity homotopy and its constant track. *)

Definition forward_image_nonzero_by_reflection
  : ¬ TwoSphereCylinderHomotopy Z b
      (two_sphere_cylinder_map_resp (IdN : Z ⇒ Z) b
        (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
        (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
        bool_cocycle_sphere)
      (two_sphere_cylinder_map_resp (IdN : Z ⇒ Z) b
        (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
        (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
        (two_sphere_base Z b)).
Proof.
  intros W.
  pose proof (two_sphere_cylinder_homotopy_reflect IdN IdN b
    bool_identity_homotopy bool_identity_trajectory
    (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
    (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
    bool_cocycle_sphere (two_sphere_base Z b) W) as C.
  pose proof (@func_proper CZ BoolS value _ _ C) as H.
  change (true = false) in H. discriminate H.
Defined.

(** Even full Kan still does not select Group or raw cylinder Equivalence. *)

Fail Definition full_Kan_no_group : HasMagma CZ := ltac:(typeclasses eauto).
Fail Definition full_Kan_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Z b)
  := ltac:(typeclasses eauto).
