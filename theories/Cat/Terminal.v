From Cats Require Import Cat.Core.

(** * Terminal Objects *)

Definition is_terminal {C : Cat} (T : Ob) :=
  ∀ X, ∃ h : Hom X T, is_unique_element h.

Class HasTerminal `(C : Cat) :=
  { Term : Ob
  ; terminal_universal : is_terminal Term
  }.

Arguments Term {_ _}.
Arguments terminal_universal {_ _} _.

Definition term {C : Cat} `{!HasTerminal C} {X} : Hom X Term :=
  (terminal_universal X).1.

Theorem terminal_arrow_unique {C : Cat} `{!HasTerminal C} {X}
  : is_unique_element (@term C _ X).
Proof. exact (terminal_universal X).2. Qed.

Arguments term {_ _ _}.
Arguments terminal_arrow_unique {_ _ _}.

Notation "'1'" := Term : ob_scope.
Notation "'!'" := term : hom_scope.
Notation "'@!' X" := (@term _ _ _ X)
  (at level 34) : hom_scope.

Section Terminal.
Context `{C : Cat}.

Tactic Notation "elim_terminal" constr(H) "as" ident(h) :=
  let Hh_unique := fresh "H" h "_unique" in
  destruct H as (h & Hh_unique);
  rewrite unique_element_iff in Hh_unique.

Proposition term_id {T}
  : is_terminal T
  → ∀ h : Hom T T, h ≈ id.
Proof.
  intros HT h.
  elim_terminal (HT T) as hu.
  pose (Hid := Hhu_unique id).
  pose (Hh := Hhu_unique h).
  etransitivity; auto.
  symmetry; auto.
Qed.

Theorem terminal_unique {T1 T2 : Ob}
  : is_terminal T1 → is_terminal T2
  → T1 ≅ T2.
Proof.
  intros HT1 HT2.
  elim_terminal (HT1 T2) as h1.
  elim_terminal (HT2 T1) as h2.
  exists h2, h1; simpl.
  constructor; apply term_id; auto.
Qed.

End Terminal.

Notation "X '⦂' '≅' '1'" := (is_terminal X)
  (at level 50).



Section Terminal.
Context `{C : Cat} `{!HasTerminal C}.

Proposition term_η {X} (h : Hom X 1) : h ≈ !.
Proof. apply terminal_arrow_unique. trivial. Qed.

Proposition term_comp_l {X Y} (h : Hom X Y) : ! ∘ h ≈ !.
Proof. rewrite (term_η (! ∘ _)). cato. Qed.

End Terminal.

Hint Resolve terminal_universal : cat.
Hint Resolve term_η : cat.



(** ** Initial Objects *)

Class HasInitial (C : Cat)
  := _initial :: HasTerminal (op C).

Section Initial.
Context `{C : Cat}.

Definition is_initial (X : Ob)
  := @is_terminal (op C) X.

Context `{HI : !HasInitial C}.

Definition Init : @Ob C := @Term (op C) _.

Definition init {X} : (@Hom C) Init X
  := @term (op C) _ _.

Notation "0" := Init.
Notation "¡" := init.

Proposition initial_universal
  : is_initial Init.
Proof. exact (@terminal_universal (op C) HI). Qed.

End Initial.

Notation "0" := Init.
Notation "¡" := init.
