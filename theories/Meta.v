From Corelib Require Export Morphisms.
From Corelib Require Export Basics.
From Stdlib Require Export Utf8.
From Stdlib Require Export Setoid.
From Stdlib Require Export Datatypes.

Global Close Scope program_scope.
Global Set Universe Polymorphism.
(* Global Set Printing Universes. *)



(** * Meta: Universal Property *)

Record is_unique {X R} `{Equivalence X R}
    (P : X → Prop) (x : X) : Prop :=
  { this : P x
  ; that : ∀ y : X, P y → R y x
  }.

Section Unique.
Context {X : Type} {R : X → X → Prop} `{Equivalence X R}.

Definition is_unique' (x : X) : Prop
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
Context {X Y} (Rx : relation X) (Ry : relation Y).

Definition ProdEq : relation (X * Y)
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
