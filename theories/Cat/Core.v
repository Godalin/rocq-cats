From Stdlib Require Import Datatypes.
From Cats Require Export Meta.

Import Notations.

Declare Scope ob_scope.
Delimit Scope ob_scope with ob.
Open Scope ob_scope.

Declare Scope hom_scope.
Delimit Scope hom_scope with hom.
Open Scope hom_scope.

Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
Open Scope cat_scope.



(** * Category *)

Class Cat@{o h} :=
  { Ob : Type@{o}
  ; Hom : Ob → Ob → Type@{h}

  ; HomEq {X Y} : Hom X Y → Hom X Y → Prop
  ; axiom_hom_eq {X Y} :: IsHomEq (@HomEq X Y)

  ; id {X} : Hom X X

  ; comp {X Y Z} : Hom Y Z → Hom X Y → Hom X Z

  ; axiom_comp_proper {X Y Z}
    :: Proper (@HomEq Y Z ==> @HomEq X Y ==> @HomEq X Z) comp

  ; axiom_id_r {X Y : Ob} (f : Hom X Y)
    : HomEq (comp f id) f

  ; axiom_id_l {X Y : Ob} (f : Hom X Y)
    : HomEq (comp id f) f

  ; axiom_comp_assoc {X Y Z W}
      (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y)
    : HomEq (comp (comp f g) h) (comp f (comp g h))
  }.

Arguments HomEq {_ _%_ob _%_ob} _%_hom _%_hom.
Arguments axiom_id_l {_ _ _} _.
Arguments axiom_id_r {_ _ _} _.
Arguments axiom_comp_assoc {_ _ _ _ _} _ _ _.

Bind Scope ob_scope with Ob.
Bind Scope hom_scope with Hom.

Notation "'@Ob' C" := (@Ob C)
  (at level 35) : cat_scope.

Notation "'@Hom' C" := (@Hom C)
  (at level 35) : cat_scope.

Notation "'@HomEq[' X ',' Y  ']'" := (@HomEq _ X Y) : cat_scope.

Infix "≈" := HomEq
  (at level 50, no associativity) : cat_scope.

Notation "f '≈' g '⦂' 'Hom(' X ',' Y ')'" := (@HomEq _ X Y f g)
  (at level 50, no associativity, only printing,
    format "f  '≈'  g  '⦂'  'Hom(' X  ','  Y )") : cat_scope.

Notation "f '≉' g" := (¬ HomEq f g)
  (at level 50, no associativity) : cat_scope.

Notation "f '≉' g '⦂' 'Hom(' X ',' Y ')'" := (¬ @HomEq _ X Y f g)
  (at level 50, no associativity, only printing,
    format "f  '≉'  g  '⦂'  'Hom(' X  ','  Y )") : cat_scope.

Notation "'@id' X" := (@id _ X)
  (at level 35) : hom_scope.

Notation "f '∘' g" := (comp f g)
  (at level 40, left associativity) : hom_scope.

(** Category auto & eauto *)

Ltac cato := auto with cat; try reflexivity.
Ltac cate := eauto with cat; try reflexivity.

(** Category auto rewriting, eagerly simplifies the goal
    (with β rules and simple η rules) *)

Ltac carw := autorewrite with cat using try reflexivity.

(** Category association rewriting *)

Ltac rw_assoc_r args := rewrite (axiom_comp_assoc args); cato.
Ltac rw_assoc_l args := rewrite <- (axiom_comp_assoc args); cato.

Tactic Notation "cacr" := rewrite axiom_comp_assoc; cato.
Tactic Notation "cacr" constr(t) := rw_assoc_r t.
Tactic Notation "cacl" := rewrite <- axiom_comp_assoc; cato.
Tactic Notation "cacl" constr(t) := rw_assoc_l t.

Hint Resolve axiom_id_l : cat.
Hint Resolve axiom_id_r : cat.

Hint Rewrite @axiom_id_l : cat.
Hint Rewrite @axiom_id_r : cat.



Section CatBasic.
Context `{Cat} {X Y : Ob}.

Theorem symm_id_l {x : Hom X Y} : x ≈ id ∘ x.
Proof. symmetry. cato. Qed.

Theorem symm_id_r {x : Hom X Y} : x ≈ x ∘ id.
Proof. symmetry. cato. Qed.

End CatBasic.

Hint Resolve symm_id_l : cat.
Hint Resolve symm_id_r : cat.



Definition comp_pre `{C : Cat} {X Y Z : Ob} (f : Hom X Y)
  := (λ g : Hom Y Z, g ∘ f).

Definition comp_post `{C : Cat} {X Y Z : Ob} (f : Hom Y Z)
  := (λ g : Hom X Y, f ∘ g).

Arguments comp_pre {_ _ _ _} _ _ /.
Arguments comp_post {_ _ _ _} _ _ /.

Notation "f ^*" := (comp_pre f) (at level 35).
Notation "f _*" := (comp_post f) (at level 35).



(** Dual Category *)

Program Definition op (C : Cat) : Cat :=
 {|Ob := Ob
 ; Hom X Y := Hom Y X
 ; HomEq _ _ := HomEq
 ; id _ := id
 ; comp _ _ _ f g := comp g f
 |}.
Next Obligation.
  intros x x' Hx y y' Hy.
  rewrite Hx, Hy.
  reflexivity.
Qed.
Next Obligation. cato. Qed.
Next Obligation. cato. Qed.
Next Obligation.
  symmetry. apply axiom_comp_assoc.
Qed.



(** ** Prod Category *)

Definition ProdEq {X Y Rx Ry} `{IsHomEq X Rx} `{IsHomEq Y Ry}
    : X * Y → X * Y → Prop
  := λ '(x1, y1) '(x2, y2), Rx x1 x2 ∧ Ry y1 y2.

Program Instance ProdEq_Equivalence
    {X Y Rx Ry} `{IsHomEq X Rx} `{IsHomEq Y Ry}
  : Equivalence ProdEq.
Next Obligation. intros [x y]. simpl. split; cato. Qed.
Next Obligation. intros [x1 y1] [x2 y2] [H1 H2].
  split; symmetry; cato.
Qed.
Next Obligation.
  intros [x1 y1] [x2 y2] [x3 y3] [Hx1 Hy1] [Hx2 Hy2].
  split; etransitivity; eauto.
Qed.

Program Definition ProdCat (C D : Cat) : Cat :=
  {|Ob := @Ob C * @Ob D
  ; Hom X Y := Hom (fst X) (fst Y) * Hom (snd X) (snd Y)
  ; HomEq X Y f g := ProdEq f g
  ; id _ := (id, id)
  ; comp _ _ _ f g := (fst f ∘ fst g, snd f ∘ snd g)
  |}.
Next Obligation. split. split.
  - intros [h1 h2]. simpl. split; cato.
  - intros [h1 h2] [h3 h4] [H1 H2]. simpl.
    split; symmetry; cato.
  - intros [x1 y1] [x2 y2] [x3 y3] [Hx1 Hy1] [Hx2 Hy2].
    split; etransitivity; eauto.
Qed.
Next Obligation. intros [fc fd] [gc gd] [H1c H1d].
  intros [hc hd] [jc jd] [H2c H2d]. split; simpl.
  rewrite H1c, H2c. reflexivity. rewrite H2d, H1d. reflexivity.
Qed.
Next Obligation. simpl. split; cato. Qed.
Next Obligation. simpl. split; cato. Qed.
Next Obligation. simpl. cacr; split; try cacr; reflexivity. Qed.

Infix "×C" := ProdCat
  (at level 41).



Section Cat.
Context `{Cat}.

(** ** Composition *)

Proposition comp_l {X Y Z} (f : Hom Y Z) {x y : Hom X Y}
  : x ≈ y → f ∘ x ≈ f ∘ y.
Proof. intros Heq. rewrite Heq. cato. Qed.

Proposition comp_r {X Y Z} (f : Hom X Y) {x y : Hom Y Z}
  : x ≈ y → x ∘ f ≈ y ∘ f.
Proof. intros Heq. rewrite Heq. cato. Qed.



(** ** Inversion & Isomorphism *)

Definition is_linv_of {X Y} (f : Hom X Y) (g : Hom Y X) : Prop
  := g ∘ f ≈ id.

Definition is_rinv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := f ∘ g ≈ id.

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

Arguments iso {_} _%_ob _%_ob.

Notation "X '≅' Y" := (iso X Y)
  (at level 70, no associativity) : type_scope.

Notation "X '≅[' C ']' Y" := (@iso C X Y)
  (at level 70, no associativity,
    format "X  ≅[ C ]  Y") : type_scope.

Tactic Notation "elim_iso" ident(f) :=
  let fi := fresh f "i" in
  let Hfif := fresh "H" fi f in
  let Hffi := fresh "H" f fi in
  intros (f & fi & Hfif & Hffi).



Section Iso.
Context `{C : Cat}.

Theorem iso_refl {X}
  : X ≅ X.
Proof. exists id, id. cato. Qed.

Theorem iso_symm {X Y}
  : X ≅ Y → Y ≅ X.
Proof.
  intros [f [fi [H1 H2]]]; simpl in *.
  exists fi, f. split; cato.
Qed.

Theorem iso_trans {X Y Z}
  : X ≅ Y → Y ≅ Z → X ≅ Z.
Proof.
  intros [f [fi [Hf Hfi]]] [g [gi [Hg Hgi]]]; simpl in *.
  exists (g ∘ f), (fi ∘ gi).
  split; simpl.
  - rewrite axiom_comp_assoc.
    rewrite <- (axiom_comp_assoc gi).
    rewrite Hg, axiom_id_l. auto.
  - rewrite axiom_comp_assoc.
    rewrite <- (axiom_comp_assoc f).
    rewrite Hfi, axiom_id_l. auto.
Qed.

Global Instance iso_Equivalence : Equivalence iso.
Proof.
  split.
  - intros x. apply iso_refl.
  - intros x y. apply iso_symm.
  - intros x y z. apply iso_trans.
Qed.

End Iso.



(** Terminal *)

Class HasTerminal `(C : Cat) :=
  { Term : Ob
  ; term {X} : Hom X Term

  ; axiom_terminal {X}
    : is_unique' (@term X)
  }.

Arguments Term {_ _}.
Arguments term {_ _ _}.
Arguments axiom_terminal {_ _ _}.

Notation "'1'" := Term : ob_scope.
Notation "'!'" := term : hom_scope.
Notation "'@!' X" := (@term _ _ _ X)
  (at level 34) : hom_scope.

Section Terminal.
Context `{C : Cat}.

Definition is_terminal T :=
  ∀ X, ∃ h : Hom X T, is_unique' h.

Tactic Notation "elim_terminal" constr(H) "as" ident(h) :=
  let Hh_unique := fresh "H" h "_unique" in
  destruct H as (h & Hh_unique);
  rewrite elim_is_unique' in Hh_unique.

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



Section Terminal.
Context `{C : Cat} `{!HasTerminal C}.

Proposition term_terminal
  : is_terminal 1.
Proof.
  intros X. exists !.
  apply axiom_terminal.
Qed.

Proposition term_η {X} (h : Hom X 1) : h ≈ !.
Proof. apply axiom_terminal. trivial. Qed.

Proposition term_comp_l {X Y} (h : Hom X Y) : ! ∘ h ≈ !.
Proof. rewrite (term_η (! ∘ _)). cato. Qed.

End Terminal.

Hint Resolve term_terminal : cat.
Hint Resolve term_η : cat.

(* Hint Rewrite @term_η : cat. *)
(* Hint Rewrite @term_comp_l : cat. *)



(** * Product Object *)

Class HasProduct `(Cat) :=
  { Prod : Ob → Ob → Ob
  ; pair {X Y Z} (f : Hom Z X) (g : Hom Z Y) : Hom Z (Prod X Y)
  ; π1 {X Y} : Hom (Prod X Y) X
  ; π2 {X Y} : Hom (Prod X Y) Y

  ; axiom_pair_proper {X Y Z}
    :: Proper (@HomEq[Z,X] ==> @HomEq[Z,Y] ==> @HomEq[Z,Prod X Y]) pair

  ; axiom_product {X Y Z} {f : Hom Z X} {g : Hom Z Y}
    : is_unique (λ h, π1 ∘ h ≈ f ∧ π2 ∘ h ≈ g) (pair f g)
  }.

Arguments Prod {_ _} _%_ob _%_ob.
Arguments pair {_ _ _ _ _} _ _.
Arguments π1 {_ _ _ _}.
Arguments π2 {_ _ _ _}.
Arguments axiom_product {_ _ _ _} _ _ _.

Notation "X '×' Y" := (Prod X Y)
  (at level 41, right associativity) : ob_scope.

Notation "'⟨' f ',' g '⟩'" := (pair f g)
  (format "'⟨' f  ','  g '⟩'") : hom_scope.

Notation "'@π1' X Y" := (@π1 _ _ _ X Y)
  (at level 35) : hom_scope.

Notation "'@π2' X Y" := (@π2 _ _ _ X Y)
  (at level 35) : hom_scope.



Section Product.
Context `{C : Cat}.

Definition is_product (X Y P : Ob)
    (p : Hom P X) (q : Hom P Y) :=
  ∀ Z (f : Hom Z X) (g : Hom Z Y),
    ∃ h : Hom Z P, is_unique (λ h, p ∘ h ≈ f ∧ q ∘ h ≈ g) h.

Tactic Notation "elim_product" constr(H) "as" ident(h) :=
  let Hh1 := fresh "H" h "1" in
  let Hh2 := fresh "H" h "2" in
  let Hh_unique := fresh "H" h "_unique" in
  destruct H as (h & (Hh1 & Hh2) & Hh_unique).

Context {X Y P Q : Ob}.
Context {p1 : Hom P X} {p2 : Hom P Y}.
Context {q1 : Hom Q X} {q2 : Hom Q Y}.

(* TODO *)

Theorem product_unique
  : is_product X Y P p1 p2
  → is_product X Y Q q1 q2
  → P ≅ Q.
Admitted.

End Product.



Section Product.
Context `{C : Cat} `{!HasProduct C}.

Theorem prod_product {X Y : Ob}
  : is_product X Y (X × Y) π1 π2.
Proof.
  intros Z f g.
  exists ⟨f,g⟩.
  apply axiom_product.
Qed.

Proposition prod_β1 {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : π1 ∘ ⟨f,g⟩ ≈ f.
Proof.
  pose (AP := axiom_product Z f g).
  destruct AP as [[H1 _] _].
  auto.
Qed.

Proposition prod_β2 {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : π2 ∘ ⟨f,g⟩ ≈ g.
Proof.
  pose (AP := axiom_product Z f g).
  destruct AP as [[_ H2] _].
  auto.
Qed.

Lemma prod_comp_r {X Y Z W}
    (f : Hom Z X) (g : Hom Z Y) (h : Hom W Z)
  : ⟨f , g⟩ ∘ h ≈ ⟨f ∘ h , g ∘ h⟩.
Proof.
  apply axiom_product.
  split.
  - rewrite <- axiom_comp_assoc, prod_β1. cato.
  - rewrite <- axiom_comp_assoc, prod_β2. cato.
Qed.

Lemma prod_η {X Y Z} (h : Hom Z (X × Y))
  : h ≈ ⟨ π1 ∘ h , π2 ∘ h ⟩.
Proof.
  apply axiom_product; split; cato.
Qed.

Lemma prod_comm {X Y} : X × Y ≅ Y × X.
Proof.
  exists ⟨π2, π1⟩, ⟨π2, π1⟩.
  simpl. split.
  - rewrite prod_comp_r.
    rewrite prod_β1.
    rewrite prod_β2.
    symmetry.
    apply axiom_product.
    split; cato.
  - rewrite prod_comp_r.
    rewrite prod_β1.
    rewrite prod_β2.
    symmetry.
    apply axiom_product.
    split; cato.
Qed.

End Product.

Hint Resolve prod_product : cat.
Hint Resolve prod_β1 : cat.
Hint Resolve prod_β2 : cat.

Hint Rewrite @prod_β1 : cat.
Hint Rewrite @prod_β2 : cat.



Section Cross.
Context `{C : Cat} `{H : !HasProduct C}.

Definition cross {X Y X' Y'} (f : Hom X X') (g : Hom Y Y')
  : Hom (X × Y) (X' × Y')
  := ⟨ f ∘ π1 , g ∘ π2 ⟩.

Opaque cross.

End Cross.

Notation "f '×' g" := (cross f g)
  (at level 41, right associativity) : hom_scope.



Section Cross.
Context `{HasProduct}.

Lemma cross_η {X Y X' Y'} (f : Hom X X') (g : Hom Y Y')
  : f × g ≈ ⟨ f ∘ π1 , g ∘ π2 ⟩.
Proof. cato. Qed.

Lemma prod_comp_l {X Y X' Y' Z}
    (f : Hom Z X) (g : Hom Z Y) (f' : Hom X X') (g' : Hom Y Y')
  : (f' × g') ∘ ⟨f , g⟩ ≈ ⟨f' ∘ f , g' ∘ g⟩.
Proof.
  apply axiom_product.
  split.
  - rewrite <- axiom_comp_assoc.
    rewrite cross_η.
    rewrite prod_β1.
    rewrite axiom_comp_assoc.
    rewrite prod_β1.
    cato.
  - rewrite <- axiom_comp_assoc.
    rewrite cross_η.
    rewrite prod_β2.
    rewrite axiom_comp_assoc.
    rewrite prod_β2.
    cato.
Qed.

End Cross.



Section Product.
Context `{C : Cat}.
Context `{!HasTerminal C}.
Context `{!HasProduct C}.

Theorem term_prod_id_l {X}
  : 1 × X ≅ X.
Proof.
  exists π2, ⟨!,id⟩; simpl.
  split.
  - rewrite prod_comp_r.
    rewrite term_η.
    rewrite axiom_id_l.
    symmetry.
    apply axiom_product.
    split; cato.
  - cato.
Qed.

Theorem term_prod_id_r {X}
  : X × 1 ≅ X.
Proof.
  rewrite prod_comm.
  apply term_prod_id_l.
Qed.

Example term_1_1 {X}
  : (X × 1) × 1 ≅ X.
Proof.
  rewrite term_prod_id_r.
  rewrite term_prod_id_r.
  reflexivity.
Qed.

End Product.



(* Exponential *)

Class HasExponential {C : Cat} `(!HasProduct C) :=
  { exp : Ob → Ob → Ob
  ; curry {X Y Z} : Hom (Z × X) Y → Hom Z (exp Y X)
  ; eval {X Y} : Hom (exp Y X × X) Y

  ; axiom_curry_proper {X Y Z}
    :: Proper (@HomEq[Z × X, Y] ==> @HomEq[Z, exp Y X]) curry

  ; axiom_exponential {X Y Z}
    : ∀ f : Hom (Z × X) Y,
      is_unique (λ h, eval ∘ (h × id) ≈ f) (curry f)
  }.

Notation "X '^' Y" := (exp X Y)
  (at level 30, right associativity): ob_scope.

Notation "'ƛ' f" := (curry f)
  (at level 35) : hom_scope.

Notation "'@eval' X Y" := (@eval _ _ _ _ X Y)
  (at level 35) : hom_scope.
