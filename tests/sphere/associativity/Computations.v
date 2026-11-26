From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereAssociativity
  Instance.Bool.CocycleSphereGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Rebracketing and Class Associativity

    Glue coefficient-built composite tetrahedra, fill their actual
    four-horn with the integrated Kan model, and inspect all five faces.
    Then compute both bracketings of the actual selected multiplication
    and consume the general law on the previously selected class magma. *)

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Proving associativity does not register stronger selected structures. *)

Fail Definition unchosen_semigroup
  : HasMagma BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_group
  : HasMagma BoolCocycleSphereClassS
  := _.

(** Three true-labelled inputs have false-labelled intermediate products. *)

Definition first_composite
  := (CocycleTwoSphereMul (M := BoolS_Monoid)) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

Definition second_composite
  := (CocycleTwoSphereMul (M := BoolS_Monoid)) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
      (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

Definition left_composite
  := (CocycleTwoSphereMul (M := BoolS_Monoid))
      (cocycle_two_sphere_mul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) true)) (cocycle_two_sphere_resp (M := BoolS_Monoid) true).

(** Retain the actual horn and its selected four-simplex filler. *)

Definition assoc_horn
  := SphereAssociativityHornN BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      first_composite second_composite left_composite.

Definition assoc_filler
  := horn_fill assoc_horn.

(** Exercise both the supplied-filler and minimal chosen interfaces. *)

Definition given_rebracketing
  := SphereCompositeReassociateOfFiller BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) first_composite second_composite
      left_composite assoc_filler.1 assoc_filler.2.

Definition chosen_rebracketing
  := SphereCompositeReassociate BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      first_composite second_composite left_composite.

(** Inspect the four triangular faces of a tetrahedron. *)

Definition face_values (w : BoolCocycleModel 3)
  : bool * bool * bool * bool
  := (two_cocycle_triangle_value_resp (M := BoolS_Monoid) (d[BoolCocycleModel; 2; fin_first] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) (d[BoolCocycleModel; 2; fin_first⁺⁺] w),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] w)).

Example actual_horn_computes
  : (face_values (d[BoolCocycleModel; 3; fin_first] assoc_filler.1),
     face_values (d[BoolCocycleModel; 3; fin_first⁺] assoc_filler.1),
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺] assoc_filler.1),
     face_values given_rebracketing.1,
     face_values (d[BoolCocycleModel; 3; fin_first⁺⁺⁺⁺] assoc_filler.1),
     face_values chosen_rebracketing.1)
      = ((false, false, false, false), (false, true, false, true),
         (false, true, true, false), (false, false, true, true),
         (false, true, false, true), (false, false, true, true)).
Proof. vm_compute. reflexivity. Defined.

(** Keep the actual selected multiplication for both bracketings. *)

Definition three_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := _.

Definition bracket_values (a b c : bool)
  : bool * bool
  := (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid)
        (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
          three_choice
          (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
            three_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
            (cocycle_two_sphere_resp (M := BoolS_Monoid) b))
          (cocycle_two_sphere_resp (M := BoolS_Monoid) c)),
      (cocycle_two_sphere_class_value_resp (M := BoolS_Monoid))
        (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
          three_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) a)
          (two_sphere_kan_mul BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
            three_choice (cocycle_two_sphere_resp (M := BoolS_Monoid) b) (cocycle_two_sphere_resp (M := BoolS_Monoid) c)))).

Example all_bracketings_compute
  : (bracket_values false false false, bracket_values false false true,
     bracket_values false true false, bracket_values false true true,
     bracket_values true false false, bracket_values true false true,
     bracket_values true true false, bracket_values true true true)
      = ((false, false), (true, true), (true, true), (false, false),
         (true, true), (false, false), (false, false), (true, true)).
Proof. vm_compute. reflexivity. Defined.

(** Compare unrelated supplied composites through the actual horn proof. *)

Example supplied_outputs_associate
  : (cocycle_two_sphere_mul (M := BoolS_Monoid)
        (cocycle_two_sphere_mul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
          (cocycle_two_sphere_resp (M := BoolS_Monoid) true)) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
      : BoolCocycleSphereClassS) ≈S
      (cocycle_two_sphere_mul (M := BoolS_Monoid)) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
        (cocycle_two_sphere_mul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
          (cocycle_two_sphere_resp (M := BoolS_Monoid) true)).
Proof.
  exact (two_sphere_composite_assoc BoolCocycleModel
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) first_composite second_composite left_composite
    (CocycleTwoSphereMul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
      (cocycle_two_sphere_mul (M := BoolS_Monoid) (cocycle_two_sphere_resp (M := BoolS_Monoid) true)
        (cocycle_two_sphere_resp (M := BoolS_Monoid) true)))).
Defined.

(** Use exactly the existing selected magma, without choosing a semigroup. *)

Definition class_magma
  : Magma
  := TwoSphereClassMagma BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
      three_choice.

Example magma_associates (x y z : BoolCocycleSphereClassS)
  : @mul _ (hasMagma class_magma) (@mul _ (hasMagma class_magma) x y) z ≈S
      @mul _ (hasMagma class_magma) x (@mul _ (hasMagma class_magma) y z).
Proof.
  exact (two_sphere_kan_mul_assoc BoolCocycleModel
    (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) three_choice x y z).
Defined.
