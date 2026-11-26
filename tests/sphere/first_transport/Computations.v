From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereFirstTransport
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Transport and a Generated Chain

    Build the input homotopy using the already proved four-horn comparison
    between a generic selected product and a coefficient-built product.
    Both new transports consume the actual Boolean Kan fillers. The finite
    generated chain contains equality, homotopy, symmetry and transitivity;
    computing its returned tetrahedron exercises the existing closure fold. *)

Fail Definition unchosen_group
  : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid)
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Fail Definition unchosen_forward_horn
  : HasHornFillers BoolCocycleModel 4 fin_first⁺⁺⁺
  := _.

Local Existing Instance BoolCocycleModel_HasKanFillers.

(** The two input representatives have coefficient true, but come from
    different constructions. Their boundary witnesses are retained. *)

Definition selected_input
  := SphereKanComposite BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) false) (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

Definition direct_input
  := (cocycle_two_sphere_mul (M := BoolS_Monoid))
      (cocycle_two_sphere_resp (M := BoolS_Monoid) false) (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

(** The input homotopy is an actual tetrahedron from the earlier comparison. *)

Definition input_homotopy
  : TwoSphereHomotopy BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      selected_input.1 direct_input
  := SphereCompositeOutputHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) selected_input.2
      (CocycleTwoSphereMul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) false)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).

(** Compose the first representative with the true-labelled sphere. *)

Definition initial_composite
  := (CocycleTwoSphereMul (M := BoolS_Monoid)) selected_input.1 (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

(** Transport forward, then back, retaining the same output representative. *)

Definition forward_composite
  := SphereCompositeFirstHomotopy BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) input_homotopy initial_composite.

Definition backward_composite
  := SphereCompositeFirstHomotopyBack BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) input_homotopy forward_composite.

(** Keep an explicit generated derivation; it is not replaced by reflexivity. *)

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

(** Fold the whole chain into a new actual composite tetrahedron. *)

Definition chain_composite
  := fst (two_sphere_composite_first_class BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) input_chain
      (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
      (cocycle_two_sphere_mul (M := BoolS_Monoid) selected_input.1 (cocycle_two_sphere_resp (M := BoolS_Monoid) true)))
      initial_composite.

(** Read all triangle faces, including nonconstant input and context faces. *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (M := BoolS_Monoid) (d[BoolCocycleModel; 2; fin_first] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example transports_compute
  : (face_values input_homotopy.1, face_values forward_composite.1,
     face_values backward_composite.1, face_values chain_composite.1)
      = ((false, false, true, true), (false, true, false, true),
         (false, true, false, true), (false, true, false, true)).
Proof. vm_compute. reflexivity. Defined.

(** A three-horn choice is explicit data, not a new registered instance. *)

Definition three_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

(** The partial class operation retains the selected product computation. *)

Definition partial_value (a b : bool)
  : bool
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
      (two_sphere_kan_composite_first_resp BoolCocycleModel
        (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice
        (cocycle_two_sphere_resp (M := BoolS_Monoid) b) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)).

Example partial_operation_computes
  : (partial_value false false, partial_value false true,
     partial_value true false, partial_value true true)
      = (false, true, true, false).
Proof. vm_compute. reflexivity. Defined.

(** Consume the actual class-map Proper field on the full generated chain. *)

Example partial_preserves_chain
  : two_sphere_kan_composite_first_resp BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
      selected_input.1 ≈S
      two_sphere_kan_composite_first_resp BoolCocycleModel
        (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
        direct_input.
Proof. apply func_proper. exact input_chain. Defined.
