(* From Stdlib Require Export Morphisms.
From Stdlib Require Export Setoid.
From Stdlib Require Export Basics. *)
From Stdlib Require Export CMorphisms.
From Stdlib Require Export CEquivalence.
From Stdlib Require Export Datatypes.
From Stdlib Require Utf8.

Global Close Scope program_scope.
Global Set Universe Polymorphism.

Global Set Warnings "-notation-overridden".
Global Set Warnings "-notation-incompatible-format".



(** * Type Notation *)

Module Export TypeLogic.
Export Utf8.

(* Notation "'∀' x .. y , P" := (forall x, .. (forall y, P)..)
  (at level 10, x binder, y binder, P at level 200,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope. *)

Local Disable Notation "∃ x .. y , P".
Notation "∃ x .. y , P" := (sigT (λ x, .. (sigT (λ y, P))..))
  (at level 10, x binder, y binder, P at level 200,
  format "'[ ' '[ ' ∃  x .. y ']' , '/' P ']'") : type_scope.

Notation "x ∨ y" := (sum x y)
  (at level 85, right associativity, only parsing) : type_scope.
Notation "x ∧ y" := (prod x y)
  (at level 80, right associativity, only parsing) : type_scope.

Notation "x ↔ y" := (iffT x y)
  (at level 95, no associativity, only parsing): type_scope.
Notation "¬ x" := (x → Empty_set)
  (at level 75, right associativity) : type_scope.

Export SigTNotations.
Export Notations.
End TypeLogic.



(** * Meta: Universal Property *)

Record is_unique {X R} `{Equivalence X R}
    (P : X → Type) (x : X) : Type :=
  { this : P x
  ; that : ∀ y : X, P y → R y x
  }.

Section Unique.
Context {X : Type} {R : X → X → Type} `{Equivalence X R}.

Definition is_unique' (x : X) : Type
  := is_unique (λ _, True) x.

Theorem elim_is_unique' {x : X}
  : is_unique' x ↔ ∀ y : X, R y x.
Proof. firstorder. Qed.

End Unique.

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



(** ** Equivalence of Prod Types *)

Section ProdEquivalence.
Context {X Y} (Rx : crelation X) (Ry : crelation Y).

Definition ProdEq : crelation (X * Y)
  := λ '(x1, y1) '(x2, y2), Rx x1 x2 ∧ Ry y1 y2.

Context `{Equivalence X Rx} `{Equivalence Y Ry}.

Global Program Instance ProdEq_Equivalence : Equivalence ProdEq.
Next Obligation. intros [x y]. simpl. split; reflexivity. Qed.
Next Obligation. intros [x1 y1] [x2 y2] [H1 H2].
  split; symmetry; auto.
Qed.
Next Obligation.
  intros [x1 y1] [x2 y2] [x3 y3] [Hx1 Hy1] [Hx2 Hy2].
  split; etransitivity; eauto.
Qed.

End ProdEquivalence.
