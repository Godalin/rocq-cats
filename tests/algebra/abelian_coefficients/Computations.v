From Cats Require Import
  Algebra.Group.Equation
  Instance.Bool.Commutative.

Local Open Scope algebra_scope.

(** * Explicitly Selected Boolean Coefficients

    Importing coefficients must not make their chosen structures automatic.
    After local enabling, solution projections should compute actual bits. *)

Fail Definition unchosen_boolean_group
  : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid)
  := ltac:(typeclasses eauto).

Fail Definition unchosen_boolean_commutativity
  : IsCommMagma BoolS_Monoid
  := ltac:(typeclasses eauto).

(** ** Computing the Selected Solutions

    Enable the existing xor group and its commutativity witness locally,
    checking that both refer to the same underlying multiplication. *)

Section BooleanComputations.
Local Existing Instance BoolS_IsCommMagma.

Example left_solution_computes
  : (GroupMulLSolution (G := BoolS_Group) true false).1 = true.
Proof. reflexivity. Qed.

Example right_solution_computes
  : (GroupMulRSolution (G := BoolS_Group) true false).1 = true.
Proof. reflexivity. Qed.

Example left_solution_map_computes
  : (mul_l_solve_resp (G := BoolS_Group)) true true = false.
Proof. reflexivity. Qed.

Example right_solution_map_computes
  : (mul_r_solve_resp (G := BoolS_Group)) false true = true.
Proof. reflexivity. Qed.

(** The group and commutativity witnesses infer coherently without a second
    explicitly enabled monoid instance. *)

Definition boolean_interchange (a b c d : BoolS)
  : @mul _ (hasMagma BoolS_Monoid)
      (@mul _ (hasMagma BoolS_Monoid) a b) (@mul _ (hasMagma BoolS_Monoid) c d) ≈S
      @mul _ (hasMagma BoolS_Monoid)
        (@mul _ (hasMagma BoolS_Monoid) a c) (@mul _ (hasMagma BoolS_Monoid) b d)
  := mul_interchange (M := BoolS_Semigroup) a b c d.

End BooleanComputations.
