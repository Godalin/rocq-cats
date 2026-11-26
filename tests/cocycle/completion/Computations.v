From Cats Require Import
  Algebra.Group.Cocycle
  Instance.Bool.Commutative.

Local Open Scope algebra_scope.

(** * Actual Boolean Completion Labels

    Importing the theory does not choose a coefficient structure. The
    concrete checks below then enable the existing Boolean group locally
    and inspect the selected labels, rather than their proof fields. *)

Fail Definition unchosen_boolean_group
  : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid)
  := _.

Fail Definition unchosen_boolean_commutativity
  : IsCommMagma BoolS_Monoid
  := _.


(** The first projection computes without unfolding an opaque theorem. *)

Example first_label_computes
  : (Cocycle012Solution (G := BoolS_Group) true true false).1 = false.
Proof. reflexivity. Defined.

(** Solving for the second label retains a nonunit answer. *)

Example second_label_computes
  : (Cocycle023Solution (G := BoolS_Group) true false false).1 = true.
Proof. reflexivity. Defined.

(** Reorienting the equation does not obscure the third computation. *)

Example third_label_computes
  : (Cocycle123Solution (G := BoolS_Group) true true false).1 = false.
Proof. reflexivity. Defined.

(** The fourth completion also remains transparent. *)

Example last_label_computes
  : (Cocycle013Solution (G := BoolS_Group) false true false).1 = true.
Proof. reflexivity. Defined.
