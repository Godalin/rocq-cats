From Corelib Require Export Morphisms.
From Corelib Require Export Basics.
From Stdlib Require Export Utf8.
From Stdlib Require Export Setoid.

Global Close Scope program_scope.
Global Set Universe Polymorphism.
(* Global Set Printing Universes. *)

(** * Meta: Universal Property *)

(** Hom-set Equality *)

Class IsHomEq {H} (R : H → H → Prop) :=
  { hom_eq_equiv :: Equivalence R
  }.

Record is_unique {X R} `{IsHomEq X R} (P : X → Prop) (x : X) : Prop :=
  { this : P x
  ; that : ∀ y : X, P y → R y x
  }.

Section Unique.
Context {X : Type} {R : X → X → Prop} `{IsHomEq X R}.

Definition is_unique' (x : X) : Prop
  := is_unique (λ _, True) x.

Theorem elim_is_unique' {x : X}
  : is_unique' x ↔ ∀ y : X, R y x.
Proof. firstorder. Qed.

Tactic Notation "elim_unique" constr(H) "as" ident(Hyp) :=
  let Hsat := fresh Hyp "_sat" in
  let Heq := fresh Hyp "_eq" in
  destruct H as [Hsat Heq].

Tactic Notation "elim_unique'" constr(H) "as" ident(Hyp) :=
  let Heq := fresh Hyp "_eq" in
  destruct H as [_ Heq].

Tactic Notation "elim_unique" constr(H) "with" constr(h) :=
  let Heq := fresh "Heq" in
  destruct H as [_ Heq];
  specialize (Heq h).

End Unique.

(* Notation "'is_universal'' x1 .. xn , C , P" :=
  (C ∧ (∀ x1, .. (∀ xn, C → P)..))
  (at level 200, x1 binder, xn binder,
    only parsing). *)

(* Check λ x y, is_universal' P x y, x = y, h, h x y = x. *)

(* Notation "'is_universal[' x1 .. xn '|' C '&∃!' h 's.t.' P ']'" :=
  (λ x1, .. (λ xn, is_universal' x1 .. xn, C, (∃ h, (λ h, P) h))..)
  (at level 200, x1 binder, xn binder, h binder,
    only parsing). *)

(* Check is_universal[x y | x = y &∃! h s.t. h x y = x]. *)
