From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereMap
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.

(** * Distinct Representations and Retained Equality Witnesses

    This constant simplicial setoid has Boolean representations and a
    Boolean-valued equality between every pair. Both false and true are
    equality witnesses; the tests must not identify either their native
    representations or their witnesses. *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation.
  split.
  - intros x. exact true.
  - intros x y E. exact E.
  - intros x y z E F. exact E.
Defined.

(** A constant simplicial object retains those representations in every degree. *)

Definition WitnessX
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

(** A retained true triangle based at false. Its boundary equalities are data. *)

Definition witness_sphere
  : TwoSphereClassS WitnessX false
  := (true; λ i, false).

(** Different specified-equality witnesses retain the exact same triangle. *)

Example base_change_computes
  : ((two_sphere_class_change_base_resp WitnessX
        (false : (false : WitnessX 0) ≈S true) witness_sphere).1,
     (two_sphere_class_change_base_resp WitnessX
        (true : (false : WitnessX 0) ≈S true) witness_sphere).1)
      = (true, true).
Proof. reflexivity. Defined.

(** Negation respects this specified relation without identifying Boolean data. *)

Program Definition flip_resp
  : WitnessS →r WitnessS
  :=
  {|func := negb
  |}.
Next Obligation. intros x y E. exact E. Defined.

(** The same negation in each degree is a natural transformation. *)

Program Definition FlipN
  : WitnessX ⇒ WitnessX
  :=
  {|nt n := flip_resp
  |}.
Next Obligation. intros x. exact true. Defined.

(** Retain its actual inverse map; inverse laws use the Boolean relation. *)

Definition flip_NatIso
  : FlipN ⦂ WitnessX ≅N WitnessX.
Proof. intros n. exists flip_resp. split; intros x; exact true. Defined.

(** The forward class map changes the triangle, and its corrected inverse
    computes back to the original representation at the original base. *)

Example class_inverse_computes
  : ((two_sphere_class_map_resp FlipN false witness_sphere).1,
     (two_sphere_class_inverse_resp FlipN flip_NatIso false
       (two_sphere_class_map_resp FlipN false witness_sphere)).1)
      = (false, true).
Proof. reflexivity. Defined.

(** Consume the witness-independent coherence on the two distinct witnesses. *)

Definition witness_coherence
  : two_sphere_class_change_base_resp WitnessX
      (false : (false : WitnessX 0) ≈S true) witness_sphere ≈S
    two_sphere_class_change_base_resp WitnessX
      (true : (false : WitnessX 0) ≈S true) witness_sphere
  := two_sphere_class_change_base_witness WitnessX false true witness_sphere.

(** An actual tetrahedron may have a different native representation from
    its faces, since its equations use the specified Boolean relation. *)

Definition witness_composite
  : TwoSphereComposite WitnessX false
      witness_sphere witness_sphere witness_sphere
  := (false; (false, (false, (false, false)))).

(** Base transport keeps the tetrahedron; mapping applies the actual
    degree-three component, which negates it in this example. *)

Example composite_data_compute
  : ((two_sphere_composite_change_base WitnessX
        (true : (false : WitnessX 0) ≈S true) witness_composite).1,
     (two_sphere_composite_map FlipN false witness_composite).1)
      = (false, true).
Proof. reflexivity. Defined.

(** Retain a genuine elementary generator between different native triangles. *)

Definition witness_homotopy
  : TwoSphereHomotopy WitnessX false witness_sphere
      (two_sphere_base WitnessX false)
  := (false; (true, (true, (false, false)))).

(** The class map consumes that tetrahedron derivation through its Proper
    field; it does not substitute native equality or compare proof fields. *)

Definition mapped_generator
  : two_sphere_class_map_resp FlipN false witness_sphere ≈S
      two_sphere_class_map_resp FlipN false (two_sphere_base WitnessX false)
  := @func_proper _ _ (two_sphere_class_map_resp FlipN false) _ _
      (two_sphere_class_step WitnessX false witness_homotopy).
