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

  ; axiom_id_r {X Y : Ob} (f : Hom X Y)
    : comp f id = f

  ; axiom_id_l {X Y : Ob} (f : Hom X Y)
    : comp id f = f

  ; axiom_comp_assoc {X Y Z W}
      (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y)
    : comp (comp f g) h = comp f (comp g h)
  }.

Notation "'@id' X" := (@id _ _ X)
  (at level 35) : cat_scope.

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

Class HasTerminal {Ob} `(C : Cat Ob) :=
  { Term : Ob
  ; term_arr {X} : Hom X Term

  ; axiom_terminal {X}
    : is_unique (λ _, True) (@term_arr X)
  }.

Arguments Term {_ _ _}.
Arguments term_arr {_ _ _ _}.
Arguments axiom_terminal {_ _ _ _}.

Notation "1" := Term : cat_scope.
Notation "!" := term_arr : cat_scope.
Notation "'@!' X" := (@term_arr _ _ _ X)
  (at level 35) : cat_scope.

(* TODO Hint Resolve for Terminal *)



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

Proposition term_is_terminal
  : is_terminal 1.
Proof.
  intros X. exists !.
  apply axiom_terminal.
Qed.

Proposition term_arr_eq {X} {h : Hom X 1}
  : h = !.
Proof.
  apply axiom_terminal. trivial.
Qed.

End Terminal.

Hint Resolve term_is_terminal : cat.
Hint Resolve term_arr_eq : cat.



(** Product *)

Class HasProduct {Ob} `(Cat Ob) :=
  { Prod : Ob → Ob → Ob
  ; pair {X Y Z} (f : Hom Z X) (g : Hom Z Y) : Hom Z (Prod X Y)
  ; π1 {X Y} : Hom (Prod X Y) X
  ; π2 {X Y} : Hom (Prod X Y) Y

  ; axiom_product {X Y Z} {f : Hom Z X} {g : Hom Z Y}
    : is_unique (λ h, π1 ∘ h = f ∧ π2 ∘ h = g) (pair f g)
  }.

Arguments Prod {_ _ _} _ _.
Arguments pair {_ _ _ _ _ _} _ _.
Arguments π1 {_ _ _ _ _}.
Arguments π2 {_ _ _ _ _}.
Arguments axiom_product {_ _ _ _ _} _ _ _.

Infix "×" := Prod
  (at level 41, right associativity) : cat_scope.

Notation "'⟨' f ',' g '⟩'" := (pair f g)
  (format "'⟨' f ',' g '⟩'") : cat_scope.

Notation "@π1 X Y" := (@π1 _ _ _ X Y)
  (at level 35).

Notation "@π2 X Y" := (@π2 _ _ _ X Y)
  (at level 35).



Section Product.
Context {Ob} `{Cat Ob}.

Definition is_product (X Y P : Ob)
    (p : Hom P X) (q : Hom P Y) :=
  ∀ Z (f : Hom Z X) (g : Hom Z Y),
    ∃ h : Hom Z P, is_unique (λ h, p ∘ h = f ∧ q ∘ h = g) h.

End Product.

Tactic Notation "elim_product" constr(H) "as" ident(h) :=
  let Hh1 := fresh "H" h "1" in
  let Hh2 := fresh "H" h "2" in
  let Hh_unique := fresh "H" h "_unique" in
  destruct H as (h & (Hh1 & Hh2) & Hh_unique).



Section Product.
Context {Ob} `{HasProduct Ob}.

Theorem prod_is_product {X Y : Ob}
  : is_product X Y (X × Y) π1 π2.
Proof.
  intros Z f g.
  exists ⟨f,g⟩.
  apply axiom_product.
Qed.

Proposition prod_arr_1 {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : π1 ∘ ⟨f,g⟩ = f.
Proof.
  pose (AP := axiom_product Z f g).
  destruct AP as [[H1 _] _].
  auto.
Qed.

Proposition prod_arr_2 {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : π2 ∘ ⟨f,g⟩ = g.
Proof.
  elim_unique (axiom_product Z f g) as H.
  destruct H_sat as [_ H2].
  auto.
Qed.

Lemma prod_arr_comp_l {X Y Z W}
    (f : Hom Z X) (g : Hom Z Y) (h : Hom W Z)
  : ⟨f,g⟩ ∘ h = ⟨f ∘ h,g ∘ h⟩.
Proof.
  apply axiom_product.
  split.
  - rewrite <- axiom_comp_assoc, prod_arr_1. auto.
  - rewrite <- axiom_comp_assoc, prod_arr_2. auto.
Qed.

End Product.

Hint Resolve prod_is_product : cat.
Hint Resolve prod_arr_1 : cat.
Hint Resolve prod_arr_2 : cat.



Section Product.
Context {Ob} `{C : Cat Ob}.
Context `{@HasTerminal Ob C}.
Context `{@HasProduct Ob C}.

Theorem term_prod_id_l {X}
  : 1 × X ≅ X.
Proof.
  exists π2, ⟨!,id⟩; simpl.
  split.
  - rewrite prod_arr_comp_l, term_arr_eq, axiom_id_l.
    symmetry.
    apply axiom_product.
    split; cato.
  - cato.
Qed.

End Product.
