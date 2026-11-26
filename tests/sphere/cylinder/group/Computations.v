From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereCylinderGroup
  Instance.Set.Simplicial.Cocycle.SphereKanGroup
  Instance.Bool.CocycleSphere
  Cat.Diagram.Core
  Cat.Core.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Computation and Actual Relative-Cylinder Group Laws

    First use a model whose equality has Boolean witnesses and native-distinct
    representatives. Independently chosen presentation/algebra fillers expose
    the exact selected product and left inverse. Then test the actual nonzero
    Boolean cocycle model; coefficient decoding remains a client, not the
    definition of the transported operations. *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation. split; red; intros; exact true. Defined.

(** A constant simplicial setoid with genuine Type-valued equality data. *)

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

(** Two native-distinct representatives also retain different boundaries. *)

Definition x
  : TwoSphereS W false
  := (false; λ i, true).

(** The second triangle keeps its own boundary witnesses. *)

Definition y
  : TwoSphereS W false
  := (true; λ i, false).

(** The actual filler returns a supplied Boolean, with no uniqueness law. *)

Program Definition one_choice (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers W n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m h'. exact true. Defined.

(** Only presentation equivalence uses these nine-choice families. *)

Definition choices (r : Ordinal 2) (v : bool) (s : Ordinal 8)
  : HasHornFillers W (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s)
  := one_choice _ _ v.

(** Enable exactly the old four-dimensional algebra choices locally. *)

Local Definition four2
  : HasHornFillers W 4 fin_first⁺⁺
  := one_choice _ _ false.

(** Associativity's choice remains independent. *)

Local Definition four3
  : HasHornFillers W 4 fin_first⁺⁺⁺
  := one_choice _ _ true.

(** Input transport's other choice is supplied separately. *)

Local Definition four4
  : HasHornFillers W 4 fin_first⁺⁺⁺⁺
  := one_choice _ _ false.

Local Existing Instance four2.
Local Existing Instance four3.
Local Existing Instance four4.

(** Presentation choices may vary without changing representative operations. *)

Definition Q (r c : bool)
  : SetC
  := TwoSphereCylinderS W false (choices fin_first r) (choices fin_first⁺ c).

(** Multiplication, left and right inverse selections are three independent
    data: true, false and true respectively. No instance is exported. *)

Definition G (r c : bool)
  : Group
  := TwoSphereCylinderGroup W false
      (choices fin_first r) (choices fin_first⁺ c)
      (one_choice _ _ true) (one_choice _ _ false) (one_choice _ _ true).

(** Compute through the full selected parent chain, not a replacement formula. *)

Example selected_operations_compute
  : ((@mul _ (hasMagma (G false true)) x y).1,
     (@mul _ (hasMagma (G false true)) y x).1,
     (@mul_unit _ _ (hasUnit (G false true))).1,
     (@inv _ _ _ (hasInverse (G false true)) x).1,
     (@inv _ _ _ (hasInverse (G false true)) y).1) =
    (true, true, false, false, false).
Proof. vm_compute. reflexivity. Defined.

(** Changing only presentation choices leaves the full selected output
    representative definitionally unchanged, including its boundary data. *)

Example presentation_choices_keep_values
  : ((@mul _ (hasMagma (G false true)) x y : TwoSphereS W false),
     (@mul_unit _ _ (hasUnit (G false true)) : TwoSphereS W false),
     (@inv _ _ _ (hasInverse (G false true)) y : TwoSphereS W false)) =
    ((@mul _ (hasMagma (G true false)) x y : TwoSphereS W false),
     (@mul_unit _ _ (hasUnit (G true false)) : TwoSphereS W false),
     (@inv _ _ _ (hasInverse (G true false)) y : TwoSphereS W false)).
Proof. vm_compute. reflexivity. Defined.

(** Recovery preserves the original triangle and its native boundary witness. *)

Example recovery_keeps_representative
  : ((two_sphere_cylinder_of_class_resp W false
        (choices fin_first false) (choices fin_first⁺ true)
        (two_sphere_class_of_cylinder_resp W false
          (choices fin_first false) (choices fin_first⁺ true) y)).1,
     y.2 fin_first) = (true, false).
Proof. vm_compute. reflexivity. Defined.

(** A genuinely non-native input equality is an actual relative cylinder. *)

Definition input_cylinder
  : TwoSphereCylinderHomotopy W false x y
  := TwoSphereConstantCylinder W false x y true.

(** Generic inverse Proper consumes that actual cylinder. *)

Definition inverse_cylinder
  : TwoSphereCylinderHomotopy W false
      (@inv _ _ _ (hasInverse (G false true)) x)
      (@inv _ _ _ (hasInverse (G false true)) y)
  := @inv_proper _ _ (@isInverse _ _ _ (hasInverse (G false true))) x y input_cylinder.

(** Generic left unit returns a cylinder between native-distinct values. *)

Definition left_unit_cylinder
  : TwoSphereCylinderHomotopy W false
      (@mul _ (hasMagma (G false true))
        (@mul_unit _ _ (hasUnit (G false true))) x) x
  := @mul_unit_l _ _ _ (@isUnit _ _ (hasUnit (G false true))) x.

(** The right-unit law is the inherited law of that same monoid. *)

Definition right_unit_cylinder
  : TwoSphereCylinderHomotopy W false
      (@mul _ (hasMagma (G false true)) y
        (@mul_unit _ _ (hasUnit (G false true)))) y
  := @mul_unit_r _ _ _ (@isUnit _ _ (hasUnit (G false true))) y.

(** Both inverse equations return actual cylinders, including the independently
    chosen right-candidate comparison already proved in the source group. *)

Definition left_inverse_cylinder
  := @mul_inv_l _ _ _ _ (@isInverse _ _ _ (hasInverse (G false true))) y.

(** Read the right law from the same selected group. *)

Definition right_inverse_cylinder
  := @mul_inv_r _ _ _ _ (@isInverse _ _ _ (hasInverse (G false true))) y.

(** The actual associativity law is obtained from its same inherited parent. *)

Definition associative_cylinder
  := @mul_assoc _ _ (isSemigroup (G false true)) x y x.

(** Generic involution and uniqueness require no sphere-specific proofs. *)

Definition involution_cylinder
  := @inv_inv (G false true) y.

(** Use the actual left-inverse cylinder as input to generic uniqueness. *)

Definition uniqueness_cylinder
  := @inv_unique (G false true) y
      (@inv _ _ _ (hasInverse (G false true)) y) left_inverse_cylinder.

(** A five-dimensional boundary shape and independently varying time exercise
    the entire relative law, rather than just its vertices. *)

Definition boundary_space
  : (∂Δ[2]) 5
  := {|lower := (δ[1; fin_first⁺] ∘
        SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4);
      sieve_precomp (BoundarySieve 2) δ[1; fin_first⁺]
        (SimplexPrismTimeF (fin_first⁺⁺ : Ordinal 4))
        (boundary_face_member fin_first⁺))|}.

(** Time varies along a different simplex operator. *)

Definition varying_time
  : (Δ[1]) 5
  := {|lower := SimplexPrismTimeF (fin_first⁺ : Ordinal 4)|}.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** All eight actual laws retain their full boundary proofs. *)

Definition complete_boundary_clients
  := (inverse_cylinder.2 5 boundary_space varying_time,
      left_unit_cylinder.2 5 boundary_space varying_time,
      right_unit_cylinder.2 5 boundary_space varying_time,
      left_inverse_cylinder.2 5 boundary_space varying_time,
      right_inverse_cylinder.2 5 boundary_space varying_time,
      associative_cylinder.2 5 boundary_space varying_time,
      involution_cylinder.2 5 boundary_space varying_time,
      uniqueness_cylinder.2 5 boundary_space varying_time).

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** A group law is specified cylinder equality, not native triangle equality. *)

Fail Definition unit_law_is_not_native
  : @mul _ (hasMagma (G false true))
      (@mul_unit _ _ (hasUnit (G false true))) x = x
  := eq_refl.
Fail Definition unchosen_model : HasMagma (Q false true)
  := ltac:(typeclasses eauto).
Fail Definition unchosen_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy W false)
  := ltac:(typeclasses eauto).

(** ** The Actual Nonzero Cocycle Model

    Supply the old Boolean model and Kan choices explicitly. Decode actual
    transported group operations and consume the actual cylinder laws;
    none of this identifies general π₂ or general Kan commutativity. *)

Local Existing Instance BoolCocycleModel_HasKanFillers.

Definition Z
  : Fct (Δ^op) SetCat
  := BoolCocycleModel.

(** The base is the model's original unit vertex. *)

Definition b
  : Z 0
  := (two_cocycle_simplex_unit (M := BoolS_Monoid)) 0.

(** Select the same actual model fillers for presentation equivalence. *)

Definition cocycle_choices (r : Ordinal 2) (s : Ordinal 8)
  := @hasHornFillers Z BoolCocycleModel_HasKanFillers
      (simplex_triangle_horn_face_dim s) (simplex_triangle_horn_missing r s).

(** The cylinder setoid retains actual full relative homotopies as equality. *)

Definition CZ
  : SetC
  := TwoSphereCylinderS Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺).

(** Multiplication uses the old three-dimensional missing-face-two choice. *)

Definition product_choice
  : HasHornFillers Z 3 fin_first⁺⁺
  := _.

(** The actual left-candidate choice remains independently supplied. *)

Definition left_choice
  : HasHornFillers Z 3 fin_first⁺⁺⁺
  := _.

(** The right-candidate choice also remains explicit. *)

Definition right_choice
  : HasHornFillers Z 3 fin_first⁺
  := _.

(** Select the transported group explicitly after all model choices. *)

Definition GZ
  : Group
  := TwoSphereCylinderGroup Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺) product_choice left_choice right_choice.

(** Decode through the original class comparison and coefficient map. *)

Definition value
  : CZ →r BoolS
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)) ∘r
      two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
        (cocycle_choices fin_first⁺).

(** Actual products still read the xor of coefficients. *)

Definition product_value (a c : bool)
  : bool
  := value (@mul _ (hasMagma GZ) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) c)).

(** Actual selected inverses retain their coefficient values. *)

Definition inverse_value (a : bool)
  : bool
  := value (@inv _ _ _ (hasInverse GZ) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)).

Example cocycle_group_computes
  : (product_value false false, product_value false true,
     product_value true false, product_value true true,
     value (@mul_unit _ _ (hasUnit GZ)), inverse_value false, inverse_value true) =
    (false, true, true, false, false, false, true).
Proof. vm_compute. reflexivity. Defined.

(** Coefficient multiplication preservation reuses the old Kan comparison. *)

Definition value_product_client (a c : CZ)
  : value (@mul _ (hasMagma GZ) a c) ≈S
      @mul _ (hasMagma BoolS_Group) (value a) (value c)
  := cocycle_kan_mul_value product_choice a c.

(** Inverse preservation reuses the old actual left-candidate comparison. *)

Definition value_inverse_client (a : CZ)
  : value (@inv _ _ _ (hasInverse GZ) a) ≈S
      @inv _ _ _ (hasInverse BoolS_Group) (value a)
  := @cocycle_kan_left_inverse_value BoolS_Group left_choice a.

(** A genuine nonzero sphere is not equal to the unit even by an actual
    cylinder; use the accepted comparison to the original nonzero theorem. *)

Definition geometric_nonzero_not_unit
  : ¬ ((bool_cocycle_sphere : CZ) ≈S @mul_unit _ _ (hasUnit GZ)).
Proof.
  intros H. apply bool_cocycle_sphere_not_null.
  exact (@func_proper _ _
    (two_sphere_class_of_cylinder_resp Z b (cocycle_choices fin_first)
      (cocycle_choices fin_first⁺)) _ _ H).
Defined.

(** A real generic left-inverse law supplies the full cocycle cylinder. *)

Definition cocycle_inverse_cylinder
  : TwoSphereCylinderHomotopy Z b
      (@mul _ (hasMagma GZ) (@inv _ _ _ (hasInverse GZ) bool_cocycle_sphere)
        bool_cocycle_sphere) (@mul_unit _ _ (hasUnit GZ))
  := @mul_inv_l _ _ _ _ (@isInverse _ _ _ (hasInverse GZ)) bool_cocycle_sphere.

Local Opaque TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Its full boundary proof is usable at an independently varying time. *)

Definition cocycle_inverse_full_boundary
  := cocycle_inverse_cylinder.2 5 boundary_space varying_time.

Local Transparent TwoSphereClassCylinder TwoSphereCylinderEquivalence.

(** Even explicitly enabled full Kan still selects no cylinder Group,
    commutativity property or raw directed-cylinder Equivalence. *)

Fail Definition full_Kan_no_group : HasMagma CZ := ltac:(typeclasses eauto).
Fail Definition full_Kan_no_raw_equivalence
  : Equivalence (TwoSphereCylinderHomotopy Z b)
  := ltac:(typeclasses eauto).
