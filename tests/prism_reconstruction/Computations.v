From Cats Require Import
  Cat.Diagram.PrismReconstruction
  Cat.Diagram.Core
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * A Directed Time Edge Survives Reconstruction

    Use the generating arrow of the walking arrow as a transformation
    between constant functors. Its component is not invertible. Both
    boundaries and the recovered time arrow must compute transparently. *)

Definition InitialF
  : Fct ArrowShape ArrowShape
  := ConstF ArrowShape (C := ArrowShape) false.

Definition FinalF
  : Fct ArrowShape ArrowShape
  := ConstF ArrowShape (C := ArrowShape) true.

Program Definition DirectedN
  : InitialF ⇒ FinalF
  :=
  {|nt x := tt
  |}.
Next Obligation. exact tt. Defined.

(** The reverse component would be an inhabitant of the empty hom. *)

Example directed_not_invertible
  : (DirectedN ⦂ InitialF ≅N FinalF) → Empty_set.
Proof. intros H. exact (H false).1. Defined.

(** The extracted boundaries retain their distinct concrete objects. *)

Example initial_boundary_computes
  : AtRF (NatPrismF DirectedN) fin_first true = false.
Proof. reflexivity. Qed.

Example final_boundary_computes
  : AtRF (NatPrismF DirectedN) (fin_next fin_first) false = true.
Proof. reflexivity. Qed.

(** Extraction returns the actual noninvertible witness. Native equality
    here only compares the concrete unit-valued hom of the walking arrow. *)

Example directed_time_edge_computes
  : PrismTransformationN (NatPrismF DirectedN) false = tt.
Proof. reflexivity. Qed.

(** The inverse of reconstruction remains an explicitly stored identity. *)

Example reconstruction_inverse_computes
  : ((prism_reconstruction_iso (NatPrismF DirectedN)).2
      (false, fin_first)).1 = tt.
Proof. reflexivity. Qed.
