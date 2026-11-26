From Cats.Set.Closure Require Import Composition.
From Cats.Instance.Preorder Require Import Closure.
From Cats Require Import Cat.Core.

(** * Closure Interface Regressions

    Separate carrier and witness levels, then check computations where order
    witnesses carry numbers and equivalent objects are not natively equal.
    These tests exercise the abstract interface, rather than a syntax model. *)

Section SeparatedLevels.
Universes u r.
Constraint u < r.
Context (X : Type@{u}) (R : X → X → Type@{r}).
Context `{HR : !PreOrder R} (c d : Clos R).
Context (h : is_closure_interchange c d).

(** Closure laws and their composite retain the larger witness universe. *)

Definition separated_composite_closure
  : Clos R
  := CompositeClos c d h.

(** The category of closed objects retains its proof-bearing object data. *)

Definition separated_closed_category
  : Cat
  := ClosedCat c.

(** Reflection and idempotent multiplication work at the same separated
    levels, without resizing the closed-object witnesses. *)

Definition separated_closure_adj
  := ClosAdj c.
Definition separated_closure_monad_iso (x : X)
  := closure_monad_mul_iso c x.

End SeparatedLevels.

Section ReverseLevels.
Universes u r.
Constraint r < u.
Context (X : Type@{u}) (R : X → X → Type@{r}).
Context `{HR : !PreOrder R} (c : Clos R).

(** The abstract closure interface also permits smaller order witnesses. *)

Definition low_witness_closure_universal {x y : X} (hy : is_closed c y)
  : R (c x) y ↔ R x y
  := closure_universal c hy.
Definition low_witness_closure_reflection
  := ClosAdj c.

End ReverseLevels.

Section WitnessComputation.

(** Every comparison carries a natural-number witness. No antisymmetry or
    equality of parallel witnesses is assumed by this Type-valued preorder. *)

Definition WitnessOrder (_ _ : bool)
  : Type
  := nat.

Local Program Instance witness_order_PreOrder
  : PreOrder WitnessOrder
  :=
  {|PreOrder_Reflexive x := 0
  ; PreOrder_Transitive x y z h k := (h + k)%nat
  |}.

(** Negation is a closure for this preorder, despite not being idempotent
    under native Boolean equality. The laws return observable witness data. *)

Program Definition WitnessClosure
  : Clos WitnessOrder
  :=
  {|closure_map := negb
  |}.
Next Obligation.
  split; [intros x y h; exact (S h) |].
  split; intros x; [exact 7 | exact 11].
Defined.

(** Extending and restricting comparisons compute through the chosen laws. *)

Example closure_extension_computes
  : closure_extend WitnessClosure (x := true) (y := false) 5 2 = 8.
Proof. reflexivity. Qed.
Example closure_restriction_computes
  : closure_restrict WitnessClosure (x := true) (y := false) 2 = 9.
Proof. reflexivity. Qed.

(** The categorical hom correspondence retains these computations. *)

Example closure_adjunct_computes
  : closure_adjunct_resp WitnessClosure true (false; 5) 2 = 9.
Proof. reflexivity. Qed.
Example closure_unadjunct_computes
  : closure_unadjunct_resp WitnessClosure true (false; 5) 2 = 8.
Proof. reflexivity. Qed.

(** Native idempotence would reject this valid preorder closure. *)

Example closure_need_not_be_natively_idempotent
  : WitnessClosure (WitnessClosure true) = WitnessClosure true → Empty_set.
Proof. discriminate. Defined.

End WitnessComputation.
