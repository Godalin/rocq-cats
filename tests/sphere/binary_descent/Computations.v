From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereMagma
  Instance.Set.Magma
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Two Actual Input Chains and the Packaged Multiplication

    Both input equalities retain explicit generated derivations from
    actual four-horn comparisons. Transport them together, inspect the
    resulting tetrahedron, and consume the packaged product map's Proper
    field on that pair. Raw operations remain selected Kan computations. *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Fail Definition unchosen_outer_horn
  : HasHornFillers BoolCocycleModel 4 fin_first⁺⁺⁺⁺
  := _.

Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Even after enabling all Kan choices, class magma selection stays
    explicit rather than becoming a model instance. *)

Fail Definition unchosen_class_magma
  : HasMagma BoolCocycleSphereClassS
  := _.

(** Two selected composites with swapped inputs yield true-labelled
    representatives, independently compared to their direct products. *)

Definition first_input
  := SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) false) (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

Definition second_input
  := SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) true) (cocycle_two_sphere_resp (M := BoolS_Monoid) false).

Definition first_direct
  := (cocycle_two_sphere_mul (M := BoolS_Monoid))
      (cocycle_two_sphere_resp (M := BoolS_Monoid) false) (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

Definition second_direct
  := (cocycle_two_sphere_mul (M := BoolS_Monoid))
      (cocycle_two_sphere_resp (M := BoolS_Monoid) true) (cocycle_two_sphere_resp (M := BoolS_Monoid) false).

(** These homotopies are the actual output comparison tetrahedra. *)

Definition first_homotopy
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) first_input.2
      (CocycleTwoSphereMul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) false)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).

Definition second_homotopy
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) second_input.2
      (CocycleTwoSphereMul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) false)).

(** The first derivation explicitly retains equality, symmetry and
    transitivity in addition to its elementary homotopy. *)

Definition first_chain
  : (first_input.1 : BoolCocycleSphereClassS) ≈S first_direct
  := closure_trans (closure_refl first_input.1)
      (closure_trans (two_sphere_class_eq BoolCocycleModel
        (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (reflexivity first_input.1))
        (closure_trans (two_sphere_class_step BoolCocycleModel
          (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) first_homotopy)
          (closure_trans (closure_sym (two_sphere_class_step BoolCocycleModel
            (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) first_homotopy))
            (two_sphere_class_step BoolCocycleModel
              (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) first_homotopy)))).

(** The second argument also changes along a retained actual derivation. *)

Definition second_chain
  : (second_input.1 : BoolCocycleSphereClassS) ≈S second_direct
  := closure_trans (closure_refl second_input.1)
      (closure_trans (two_sphere_class_step BoolCocycleModel
        (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) second_homotopy)
        (closure_trans (closure_sym (two_sphere_class_step BoolCocycleModel
          (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) second_homotopy))
          (two_sphere_class_step BoolCocycleModel
            (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) second_homotopy))).

(** Transport a supplied composite both ways through both input chains,
    keeping exactly the same output representative. *)

Definition initial_composite
  := (CocycleTwoSphereMul (M := BoolS_Monoid)) first_input.1 second_input.1.

Definition forward_composite
  := fst (two_sphere_composite_class BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) first_chain second_chain
      (cocycle_two_sphere_mul (M := BoolS_Monoid) first_input.1 second_input.1))
      initial_composite.

Definition backward_composite
  := snd (two_sphere_composite_class BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) first_chain second_chain
      (cocycle_two_sphere_mul (M := BoolS_Monoid) first_input.1 second_input.1))
      forward_composite.

(** Inspect every triangular face of each actual tetrahedron. *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (M := BoolS_Monoid) (d[BoolCocycleModel; 2; fin_first] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example binary_transport_computes
  : (face_values first_homotopy.1, face_values second_homotopy.1,
     face_values forward_composite.1, face_values backward_composite.1)
      = ((false, false, true, true), (false, false, true, true),
         (false, true, false, true), (false, true, false, true)).
Proof. vm_compute. reflexivity. Defined.

(** Choose a magma explicitly, with actual Kan three-horn selection. *)

Definition three_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Definition class_magma
  : Magma
  := TwoSphereClassMagma BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      three_choice.

(** Use the generic product-map construction rather than a new wrapper. *)

Definition product_value (a b : bool)
  : bool
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
      (set_magma_mul_resp class_magma
        (cocycle_two_sphere_resp (M := BoolS_Monoid) a, (cocycle_two_sphere_resp (M := BoolS_Monoid)) b)).

Example magma_computes
  : (product_value false false, product_value false true,
     product_value true false, product_value true true)
      = (false, true, true, false).
Proof. vm_compute. reflexivity. Defined.

(** The packaged operation retains an actual composite, not just a label. *)

Example chosen_tetrahedron_computes
  : face_values (TwoSphereKanMulComposite BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice first_input.1 second_input.1).1
      = (false, true, false, true).
Proof. vm_compute. reflexivity. Defined.

(** Consume the product map's Proper field with both actual input chains. *)

Example product_preserves_both_chains
  : set_magma_mul_resp class_magma (first_input.1, second_input.1) ≈S
      set_magma_mul_resp class_magma (first_direct, second_direct).
Proof. apply func_proper. split; [exact first_chain | exact second_chain]. Defined.

(** Arbitrary supplied composites, not merely selected outputs, are
    compared through the same two generated input equalities. *)

Example supplied_outputs_agree
  : (cocycle_two_sphere_mul (M := BoolS_Monoid) first_input.1 second_input.1
      : BoolCocycleSphereClassS) ≈S
      (cocycle_two_sphere_mul (M := BoolS_Monoid)) first_direct second_direct.
Proof.
  exact (two_sphere_composite_output_class_eq BoolCocycleModel
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) initial_composite
    (CocycleTwoSphereMul (M := BoolS_Monoid) first_direct second_direct) first_chain second_chain).
Defined.
