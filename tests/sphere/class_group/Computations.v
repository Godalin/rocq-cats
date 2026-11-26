From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereGroup
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.
Local Open Scope algebra_scope.

(** * Actual Group Computation and Generic Inverse Theory

    Select the group explicitly from the actual Boolean Kan fillers.
    Its parent multiplication and unit retain their computations, and
    inversion is the actual left-candidate sphere. Generic inverse theory
    is exercised on a full generated chain from an actual four-horn. *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Even full Kan enabling leaves every algebraic model explicitly chosen. *)

Fail Definition unchosen_class_magma
  : HasMagma BoolCocycleSphereClassS
  := _.

(** Multiplication and inverse fillers remain separately supplied data. *)

Definition three_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Definition left_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺⁺
  := _.

Definition right_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺
  := _.

Definition class_group
  : Group
  := TwoSphereClassGroup BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      three_choice left_choice right_choice.


(** Read the parent's exact selected magma without another choice. *)

Definition class_magma
  : Magma
  := SemigroupToMagma (MonoidToSemigroup (GroupToMonoid class_group)).

(** Compute multiplication through the inherited parent and inversion
    through the group interface, without coefficient-operation replacements. *)

Definition product_value (a b : bool)
  : bool
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
      (@mul _ (hasMagma class_magma)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) a) (cocycle_two_sphere_resp (M := BoolS_Monoid) b)).

Definition inverse_value (a : bool)
  : bool
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
      (@inv _ _ _ (hasInverse class_group) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)).

Example parent_and_inverse_compute
  : (product_value false false, product_value false true,
     product_value true false, product_value true true,
     (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
       (@mul_unit _ _ (hasUnit (GroupToMonoid class_group))),
     inverse_value false, inverse_value true)
      = (false, true, true, false, false, false, true).
Proof. vm_compute. reflexivity. Defined.

(** The selected inverse remains the actual left-candidate triangle. *)

Example candidate_computes
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid)
        (d[BoolCocycleModel; 2; fin_first]
          (@SphereKanLeftInverse BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
            left_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).2.1),
     (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺]
          (@SphereKanLeftInverse BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
            left_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).2.1),
     (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺]
          (@SphereKanLeftInverse BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
            left_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).2.1),
     (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺]
          (@SphereKanLeftInverse BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
            left_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).2.1),
     inverse_value true)
      = (false, true, false, true, true).
Proof. vm_compute. reflexivity. Defined.

(** Use an actual comparison homotopy as a nonconstant input generator. *)

Definition selected_input
  := SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) false) (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

Definition direct_input
  := (cocycle_two_sphere_mul (M := BoolS_Monoid)) (cocycle_two_sphere_resp (M := BoolS_Monoid) false)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

Definition input_homotopy
  : TwoSphereHomotopy BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      selected_input.1 direct_input
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) selected_input.2
      (CocycleTwoSphereMul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) false)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).

Definition input_chain
  : (selected_input.1 : BoolCocycleSphereClassS) ≈S direct_input
  := closure_trans (closure_refl selected_input.1)
      (closure_trans (two_sphere_class_eq BoolCocycleModel
        (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (reflexivity selected_input.1))
        (closure_trans (two_sphere_class_step BoolCocycleModel
          (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) input_homotopy)
          (closure_trans (closure_sym (two_sphere_class_step BoolCocycleModel
            (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) input_homotopy))
            (two_sphere_class_step BoolCocycleModel
              (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) input_homotopy)))).

(** Generic inversion respects that entire generated derivation. *)

Example inverse_preserves_chain
  : @inv_resp class_group selected_input.1 ≈S
      @inv_resp class_group direct_input.
Proof. apply func_proper. exact input_chain. Defined.

(** Existing group uniqueness and involution work without sphere-specific
    replacements for their algebraic proofs. *)

Example inverse_unique (x y : BoolCocycleSphereClassS)
    (E : @mul _ (hasMagma class_magma) y x ≈S
      @mul_unit _ _ (hasUnit (GroupToMonoid class_group)))
  : y ≈S @inv _ _ _ (hasInverse class_group) x.
Proof. exact (@inv_unique class_group x y E). Defined.

Example inverse_involutive (x : BoolCocycleSphereClassS)
  : @inv _ _ _ (hasInverse class_group) (@inv _ _ _ (hasInverse class_group) x) ≈S x.
Proof. exact (@inv_inv class_group x). Defined.

Example inverse_product (x y : BoolCocycleSphereClassS)
  : @inv _ _ _ (hasInverse class_group) (@mul _ (hasMagma class_magma) x y) ≈S
      @mul _ (hasMagma class_magma)
        (@inv _ _ _ (hasInverse class_group) y) (@inv _ _ _ (hasInverse class_group) x).
Proof. exact (@inv_mul class_group x y). Defined.

(** The chosen left inverse agrees with the independently supplied right
    candidate in the generated class relation. *)

Example right_candidate_agrees (x : BoolCocycleSphereClassS)
  : @inv _ _ _ (hasInverse class_group) x ≈S (@SphereKanRightInverse BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) right_choice x).1.
Proof.
  exact (two_sphere_inverse_candidates_eq BoolCocycleModel
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice left_choice right_choice x).
Defined.
