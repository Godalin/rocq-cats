From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderGroupMap
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * A Map Which Does Not Preserve the Selected Fillers

    Boolean equality witnesses allow native-distinct triangles. Negation
    changes every chosen true filler to false, while the target independently
    selects true again. Product/inverse squares therefore commute by actual
    cylinders, even though their endpoints are not native-equal triangles. *)

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

(** Negation is respectful in the specified Type-valued relation. *)

Program Definition flip_resp
  : WitnessS →r WitnessS
  :=
  {|func := negb
  |}.
Next Obligation. intros a c E. exact E. Defined.

(** The same map is natural in every degree. *)

Program Definition FlipN
  : W ⇒ W
  :=
  {|nt n := flip_resp
  |}.
Next Obligation. intros a. exact true. Defined.

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

(** Both product and left candidate choose true; the right candidate is
    independently false. No chosen model is registered. *)

Definition G (b r c : bool)
  : Group
  := TwoSphereCylinderGroup W b (choices fin_first r) (choices fin_first⁺ c)
      (one_choice _ _ true) (one_choice _ _ true) (one_choice _ _ false).

(** This is exactly the pre-existing cylinder map, at the negated basepoint. *)

Definition mapped
  : Q false false true →r Q true true false
  := two_sphere_cylinder_map_resp FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

(** The two sides of the product and inverse squares really differ natively. *)

Example operation_square_endpoints_compute
  : ((mapped (@mul _ (hasMagma (G false false true)) x y)).1,
     (@mul _ (hasMagma (G true true false))
       (mapped x) (mapped y)).1,
     (mapped (@inv _ _ _ (hasInverse (G false false true)) x)).1,
     (@inv _ _ _ (hasInverse (G true true false)) (mapped x)).1,
     (mapped (@mul_unit _ _ (hasUnit (G false false true)))).1,
     (@mul_unit _ _ (hasUnit (G true true false))).1) =
    (false, true, false, true, true, true).
Proof. vm_compute. reflexivity. Defined.

(** The product law consumes the exact selected parent operations. *)

Definition product_cylinder
  : TwoSphereCylinderHomotopy W true
      (mapped (@mul _ (hasMagma (G false false true)) x y))
      (@mul _ (hasMagma (G true true false)) (mapped x) (mapped y))
  := two_sphere_cylinder_map_mul FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (one_choice _ _ true) (one_choice _ _ true) x y.

(** Inverse preservation compares the two actual selected inverses. *)

Definition inverse_cylinder
  : TwoSphereCylinderHomotopy W true
      (mapped (@inv _ _ _ (hasInverse (G false false true)) x))
      (@inv _ _ _ (hasInverse (G true true false)) (mapped x))
  := two_sphere_cylinder_map_left_inverse FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (one_choice _ _ true) (one_choice _ _ true)
      (one_choice _ _ true) (one_choice _ _ false) x.

(** Unit preservation consumes the units of those same groups. *)

Definition unit_cylinder
  : TwoSphereCylinderHomotopy W true
      (mapped (@mul_unit _ _ (hasUnit (G false false true))))
      (@mul_unit _ _ (hasUnit (G true true false)))
  := two_sphere_cylinder_map_unit FlipN false
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false).

(** Identity acts on the exact original presentation. *)

Definition identity_cylinder
  := two_sphere_cylinder_map_id W false
      (choices fin_first false) (choices fin_first⁺ true) y.

(** Composition retains independent intermediate and final choices. *)

Definition composition_cylinder
  := two_sphere_cylinder_map_comp
      (choices fin_first false) (choices fin_first⁺ true)
      (choices fin_first true) (choices fin_first⁺ false)
      (choices fin_first false) (choices fin_first⁺ false)
      FlipN FlipN false y.

(** Check actual image values and both composite map definitions. *)

Example image_and_composition_compute
  : ((mapped x).1, (mapped y).1,
     (two_sphere_cylinder_map_resp (FlipN ∘Nv FlipN) false
       (choices fin_first false) (choices fin_first⁺ true)
       (choices fin_first false) (choices fin_first⁺ false) y).1,
     (two_sphere_cylinder_map_resp FlipN true
       (choices fin_first true) (choices fin_first⁺ false)
       (choices fin_first false) (choices fin_first⁺ false) (mapped y)).1) =
    (true, false, true, true).
Proof. vm_compute. reflexivity. Defined.

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

(** Every new law supplies the actual complete relative boundary. *)

Definition all_five_full_boundaries
  := (product_cylinder.2 5 boundary_space varying_time,
      inverse_cylinder.2 5 boundary_space varying_time,
      unit_cylinder.2 5 boundary_space varying_time,
      identity_cylinder.2 5 boundary_space varying_time,
      composition_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** The actual witnesses do not imply native endpoint equality. *)

Fail Definition product_square_is_not_native
  : mapped (@mul _ (hasMagma (G false false true)) x y) =
      @mul _ (hasMagma (G true true false)) (mapped x) (mapped y)
  := ltac:(vm_compute; reflexivity).
Fail Definition inverse_square_is_not_native
  : mapped (@inv _ _ _ (hasInverse (G false false true)) x) =
      @inv _ _ _ (hasInverse (G true true false)) (mapped x)
  := ltac:(vm_compute; reflexivity).

(** ** Mapping the Actual Nonzero Cocycle Group

    The identity simplicial map still consumes the real model fillers and
    actual selected group operations. The nonzero inverse remains nonzero;
    only the usual xor product of the two nonzero elements is the unit. *)

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

(** The actual map is the old cylinder-map construction. *)

Definition model_mapped
  : CZ →r CZ
  := two_sphere_cylinder_map_resp (IdN : Z ⇒ Z) b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺).

(** Decode through the original class comparison, retaining the new map's
    actual output rather than replacing its selected operation. *)

Definition value
  : CZ →r BoolS
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) ∘r
      two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
        (cocycle_choices fin_first⁺).

(** Both sides of each square have their actual expected coefficients. *)

Example nonzero_map_squares_compute
  : (value (model_mapped
       (@mul _ (hasMagma GZ) bool_cocycle_sphere bool_cocycle_sphere)),
     value (@mul _ (hasMagma GZ) (model_mapped bool_cocycle_sphere)
       (model_mapped bool_cocycle_sphere)),
     value (model_mapped (@inv _ _ _ (hasInverse GZ) bool_cocycle_sphere)),
     value (@inv _ _ _ (hasInverse GZ) (model_mapped bool_cocycle_sphere)),
     value (model_mapped (@mul_unit _ _ (hasUnit GZ))),
     value (@mul_unit _ _ (hasUnit GZ))) = (false, false, true, true, false, false).
Proof. vm_compute. reflexivity. Defined.

(** The mapped product square is a real cocycle cylinder. *)

Definition cocycle_product_cylinder
  := two_sphere_cylinder_map_mul (IdN : Z ⇒ Z) b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      product_choice product_choice bool_cocycle_sphere bool_cocycle_sphere.

(** Its mapped inverse square is also a real cylinder. *)

Definition cocycle_inverse_cylinder
  := two_sphere_cylinder_map_left_inverse (IdN : Z ⇒ Z) b
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      (cocycle_choices fin_first) (cocycle_choices fin_first⁺)
      left_choice product_choice left_choice right_choice bool_cocycle_sphere.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Both model witnesses retain the full varying-time relative boundary. *)

Definition cocycle_full_boundaries
  := (cocycle_product_cylinder.2 5 boundary_space varying_time,
      cocycle_inverse_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** The actual nonzero image still cannot be the group unit by a cylinder. *)

Definition mapped_nonzero_not_unit
  : ¬ ((model_mapped bool_cocycle_sphere : CZ) ≈S @mul_unit _ _ (hasUnit GZ)).
Proof.
  intros E. pose proof (@func_proper CZ BoolS value _ _ E) as H.
  change (true = false) in H. discriminate H.
Defined.

(** Full Kan enabling still registers neither a group nor raw equivalence. *)

Fail Definition full_Kan_no_group : HasMagma CZ := ltac:(typeclasses eauto).
Fail Definition full_Kan_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Z b)
  := ltac:(typeclasses eauto).
