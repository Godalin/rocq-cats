From Cats Require Import
  Instance.Bool.CocycleHomotopy
  Cat.Core.

Import Cats.Cat.Core.

Local Open Scope nat_scope.

(** * Actual Map Data Survive the Homotopy Invariant

    Importing the obstruction must not enable chosen structures. The
    computations below inspect an actual precomposed homotopy at arbitrary
    time and evaluate a map while retaining a nontrivial chain witness. *)

Fail Definition unchosen_coefficient_group
  : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid)
  := _.

Fail Definition unchosen_class_group
  : HasMagma BoolCocycleSphereClassS
  := _.

Fail Definition unchosen_Kan
  : HasKanFillers BoolCocycleModel
  := _.


(** Evaluate the original constant homotopy restricted to a free sphere. *)

Example restricted_homotopy_computes (a : bool)
    (t : (@Hom Δ) 2 1%nat)
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (two_sphere_cylinder_eval BoolCocycleModel (two_cocycle_simplex_unit (M := BoolS_Monoid) 0)
        (CocycleHomotopySphereCylinder
          (SimplicialConstantHomotopy (IdN : BoolCocycleModel ⇒ BoolCocycleModel))
          (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (cocycle_two_sphere_resp (M := BoolS_Monoid) a)) id t) = a.
Proof. reflexivity. Defined.

(** A finite chain retains both a whole homotopy and natural equality,
    including a reversed step. This does not reverse the simplicial interval. *)

Definition identity_chain
  : (IdN : @CocycleHomotopyMapS BoolS_Monoid BoolCocycleModel) ≈S IdN.
Proof.
  transitivity (IdN : BoolCocycleModel ⇒ BoolCocycleModel).
  - exact (cocycle_homotopy_map_step (SimplicialConstantHomotopy IdN)).
  - symmetry. apply cocycle_homotopy_map_eq. reflexivity.
Defined.

(** Evaluation still computes on either representative of that chain. *)

Example chain_evaluation_computes (a : bool)
  : @cocycle_homotopy_evaluation_resp BoolS_Monoid BoolCocycleModel
      (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (cocycle_two_sphere_resp (M := BoolS_Monoid) a) IdN = a.
Proof. reflexivity. Defined.

(** Consume the chain through respectfulness, without discarding it or
    selecting any Kan filler. *)

Definition chain_evaluation_equality (a : bool)
  : a = a
  := @func_proper _ _
      (@cocycle_homotopy_evaluation_resp BoolS_Monoid BoolCocycleModel
        (two_cocycle_simplex_unit (M := BoolS_Monoid) 0) (cocycle_two_sphere_resp (M := BoolS_Monoid) a))
      _ _ identity_chain.
