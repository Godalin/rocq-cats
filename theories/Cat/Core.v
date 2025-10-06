From Stdlib Require Import Utf8.
From Stdlib Require Import Setoid.
From Cats Require Import Meta.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Open Scope cat_scope.



(** * Category *)

Class Cat (Ob : Type) :=
  { Hom : Ob → Ob → Type
  ; id {X} : Hom X X
  ; comp {X Y Z} : Hom Y Z → Hom X Y → Hom X Z

  ; axiom_id_l {X Y : Ob} (f : Hom X Y)
    : comp f id = f

  ; axiom_id_r {X Y : Ob} (f : Hom X Y)
    : comp id f = f

  ; axiom_comp_assoc {X Y Z W}
      (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y)
    : comp (comp f g) h = comp f (comp g h)
  }.

Notation "f ∘ g" := (comp f g)
  (at level 41, right associativity) : cat_scope.

Arguments axiom_id_l {Ob Cat X Y} (f).
Arguments axiom_id_r {Ob Cat X Y} (f).
Arguments axiom_comp_assoc {Ob Cat X Y Z W} (f g h).

Hint Resolve axiom_id_l : cat.
Hint Resolve axiom_id_r : cat.

Ltac cato := auto with cat.
Ltac cate := eauto with cat.



Section Cat.
Context {Ob} `{Cat Ob}.

Definition is_linv_of {X Y} (f : Hom X Y) (g : Hom Y X) : Prop
  := g ∘ f = id.

Definition is_rinv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := f ∘ g = id.

Definition is_inv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := is_linv_of f g ∧ is_rinv_of f g.

Definition is_iso {X Y} (f : Hom X Y)
  := ∃ g, is_inv_of f g.

Definition iso X Y
  := ∃ f : Hom X Y, is_iso f.

End Cat.

Hint Unfold is_linv_of : cat.
Hint Unfold is_rinv_of : cat.
Hint Unfold is_inv_of : cat.

Arguments is_linv_of {_ _ _} _ _ /.
Arguments is_rinv_of {_ _ _} _ _ /.
Arguments is_inv_of {_ _ _} _ _ /.

Infix "≅" := iso
  (at level 70, no associativity).

Tactic Notation "elim_iso" ident(f) :=
  let fi := fresh f "i" in
  let Hfif := fresh "H" fi f in
  let Hffi := fresh "H" f fi in
  intros (f & fi & Hfif & Hffi).

Section Iso.
Context {Ob} `{Cat Ob}.

Theorem iso_refl {X}
  : X ≅ X.
Proof. exists id, id. cato. Qed.

End Iso.



(** Terminal *)

Class HasTerminal {Ob} `{C : Cat Ob} :=
  { Term : Ob
  ; term_arr {X} : Hom X Term

  ; axiom_terminal {X}
    : is_unique (λ _, True) (@term_arr X)
  }.

Arguments axiom_comp_assoc {_ _ _ _ _ _ _}.

Section Terminal.
Context {Ob} `{Cat Ob}.

Definition is_terminal T :=
  ∀ X, ∃ h : Hom X T, is_unique' h.

Tactic Notation "elim_terminal" constr(H) "as" ident(h) :=
  let Hh_unique := fresh "H" h "_unique" in
  destruct H as (h & Hh_unique);
  rewrite elim_is_unique' in Hh_unique.

Proposition terminal_arr_eq_id {T}
  : is_terminal T
  → ∀ h : Hom T T, h = id.
Proof.
  intros HT h.
  elim_terminal (HT T) as hu.
  pose (Hid := Hhu_unique id).
  pose (Hh := Hhu_unique h).
  etransitivity; auto.
Qed.

Theorem terminal_unique {T1 T2 : Ob}
  : is_terminal T1 → is_terminal T2
  → T1 ≅ T2.
Proof.
  intros HT1 HT2.
  elim_terminal (HT1 T2) as h1.
  elim_terminal (HT2 T1) as h2.
  exists h2, h1; simpl.
  constructor; apply terminal_arr_eq_id; auto.
Qed.

End Terminal.



Section Terminal.
Context {Ob} `{HasTerminal Ob}.

Theorem term_arr_comp_eq_term_arr {X Y} {f : Hom X Y}
  : term_arr ∘ f = term_arr.
Proof.
  apply axiom_terminal.
  trivial.
Qed.

Proposition term_is_terminal
  : is_terminal Term.
Proof.
  intros X. exists term_arr.
  apply axiom_terminal.
Qed.

End Terminal.



(** Product *)

Class HasProduct Ob `{Cat Ob} :=
  { Prod : Ob → Ob → Ob
  ; pair {X Y Z} (f : Hom Z X) (g : Hom Z Y) : Hom Z (Prod X Y)
  ; π1 {X Y} : Hom (Prod X Y) X
  ; π2 {X Y} : Hom (Prod X Y) Y

  ; axiom_product {X Y Z} {f : Hom Z X} {g : Hom Z Y}
    : is_unique (λ h, π1 ∘ h = f ∧ π2 ∘ h = g) (pair f g)
  }.

Notation "'⟨' f ',' g '⟩'" := (pair f g) : cat_scope.

Infix "×" := Prod
  (at level 41, right associativity) : cat_scope.



Section Product.
Context {Ob} `{Cat Ob}.

Definition is_product {X Y P} (p : Hom P X) (q : Hom P Y) :=
  ∀ Z (f : Hom Z X) (g : Hom Z Y),
    ∃ h : Hom Z P, is_unique (λ h, p ∘ h = f ∧ q ∘ h = g) h.

End Product.



Section Product.
Context {Ob} `{C : Cat Ob}.
Context `{@HasTerminal Ob C}.
Context `{@HasProduct Ob C}.

Theorem term_prod_id_l {X}
  : Term × X ≅ X.
Admitted.

End Product.
