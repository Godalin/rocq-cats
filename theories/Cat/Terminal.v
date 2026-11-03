From Cats Require Import Cat.Core.

(** * Terminal Objects *)

(** * 终对象 *)

(** Every object has a unique arrow to this candidate object. *)

(** 每个对象到候选对象都有唯一箭头。 *)

Definition is_terminal {C : Cat} (T : Ob)
  := ∀ X, ∃ h : Hom X T, is_unique_element h.

(** A selected terminal object with its Type-valued universal property. *)

(** 选定终对象及其 Type 值泛性质。 *)

Class HasTerminal (C : Cat)
  :=
  { Term : Ob
  ; terminal_universal : is_terminal Term
  }.

Arguments Term {_ _}.
Arguments terminal_universal {_ _} _.

(** The universal arrow to the selected terminal object. *)

(** 指向选定终对象的泛箭头。 *)

Definition term {C : Cat} `{HT : !HasTerminal C} {X}
  : Hom X Term
  := (terminal_universal X).1.

(** The selected terminal arrow satisfies the full uniqueness property. *)

(** 选定终箭头满足完整唯一性性质。 *)

Theorem terminal_arrow_unique {C : Cat} `{HT : !HasTerminal C} {X}
  : is_unique_element (@term C _ X).
Proof. exact (terminal_universal X).2. Qed.

Arguments term {_ _ _}.
Arguments terminal_arrow_unique {_ _ _}.

Notation "'1'" := Term : ob_scope.
Notation "'!'" := term : hom_scope.
Notation "'@!' X" := (@term _ _ _ X)
  (at level 34) : hom_scope.

Section Terminal.
Context {C : Cat}.

Tactic Notation "elim_terminal" constr(H) "as" ident(h) :=
  let Hh_unique := fresh "H" h "_unique" in
  destruct H as (h & Hh_unique);
  rewrite unique_element_iff in Hh_unique.

(** Every endomorphism of a terminal object equals its identity. *)

(** 终对象的每个自同态射都等于其恒等态射。 *)

Proposition term_id {T}
  : is_terminal T
  → ∀ h : Hom T T, h ≈ id.
Proof.
  intros HT h.
  elim_terminal (HT T) as hu.
  pose (Hid := Hhu_unique id).
  pose (Hh := Hhu_unique h).
  transitivity hu; [exact Hh | symmetry; exact Hid].
Qed.

(** Two terminal objects are isomorphic through their universal arrows. *)

(** 两个终对象通过其泛箭头同构。 *)

Theorem terminal_unique {T1 T2 : Ob}
  : is_terminal T1 → is_terminal T2
  → T1 ≅ T2.
Proof.
  intros HT1 HT2. exists (HT2 T1).1, (HT1 T2).1.
  split; apply term_id; assumption.
Defined.

End Terminal.

Notation "X '⦂' '≅' '1'" := (is_terminal X)
  (at level 50).



Section Terminal.
Context {C : Cat} `{HT : !HasTerminal C}.

(** Every arrow to the selected terminal object equals the universal arrow. *)

(** 指向选定终对象的任意箭头都等于泛箭头。 *)

Proposition term_η {X} (h : Hom X 1)
  : h ≈ !.
Proof. apply terminal_arrow_unique. trivial. Qed.

(** Precomposing a terminal arrow gives the terminal arrow from its source. *)

(** 终箭头预合成后仍为其源的终箭头。 *)

Proposition term_comp_l {X Y} (h : Hom X Y)
  : ! ∘ h ≈ !.
Proof. rewrite (term_η (! ∘ _)). cato. Qed.

End Terminal.

Hint Resolve terminal_universal : cat.
Hint Resolve term_η : cat.



(** ** Initial Objects *)

(** ** 始对象 *)

(** A chosen initial object, expressed by terminality in the opposite
    category. *)

(** 通过反范畴的终性表示的选定始对象。 *)

Class HasInitial (C : Cat)
  :=
  { hasOpTerminal :: HasTerminal (C^op)
  }.

Section Initial.
Context {C : Cat}.

(** Every object receives a unique arrow from this candidate object. *)

(** 候选对象到每个对象都有唯一箭头。 *)

Definition is_initial (X : Ob)
  := @is_terminal (op C) X.

Context `{HI : !HasInitial C}.

(** The object selected by the initial-object structure. *)

(** 始对象结构选出的对象。 *)

Definition Init
  : @Ob C
  := @Term (C^op) (@hasOpTerminal C HI).

(** The universal arrow from the selected initial object. *)

(** 从选定始对象出发的泛箭头。 *)

Definition init {X}
  : (@Hom C) Init X
  := @term (C^op) (@hasOpTerminal C HI) X.

(** The selected initial object satisfies its universal property. *)

(** 选定始对象满足其泛性质。 *)

Definition initial_universal
  : is_initial Init.
Proof. exact (@terminal_universal (C^op) (@hasOpTerminal C HI)). Defined.

(** Initial-arrow uniqueness is terminal-arrow uniqueness in the opposite
    category. *)

(** 始箭头唯一性就是反范畴中的终箭头唯一性。 *)

Theorem initial_arrow_unique {X}
  : is_unique_element (@init X).
Proof. exact (@terminal_arrow_unique (C^op) (@hasOpTerminal C HI) X). Qed.

(** Every arrow from the selected initial object is its universal arrow. *)

(** 从选定始对象出发的任意箭头等于其泛箭头。 *)

Theorem init_η {X} (f : Hom Init X)
  : f ≈ init.
Proof. exact (@term_η (C^op) (@hasOpTerminal C HI) X f). Qed.

(** Postcomposition of an initial arrow is the initial arrow. *)

(** 始箭头后合成后仍为始箭头。 *)

Theorem init_comp_r {X Y} (f : Hom X Y)
  : f ∘ init ≈ init.
Proof. exact (@term_comp_l (C^op) (@hasOpTerminal C HI) Y X f). Qed.

End Initial.

Notation "0" := Init : ob_scope.
Notation "¡" := init : hom_scope.

(** Any two initial objects are isomorphic by opposite terminal uniqueness. *)

(** 由反范畴中的终对象唯一性，任意两个始对象同构。 *)

Definition initial_unique {C : Cat} {X Y : @Ob C}
    (HX : is_initial X) (HY : is_initial Y)
  : X ≅[C] Y.
Proof.
  pose (i := @terminal_unique (C^op) Y X HY HX).
  exists i.1, i.2.1. split;
    [exact (snd i.2.2) | exact (fst i.2.2)].
Defined.
