From Cats Require Export Meta.

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

Class Cat@{o h p|h <= p} :=
  { Ob : Type@{o}
  ; Hom : Ob → Ob → Type@{h}

  ; HomEq {X Y} : Hom X Y → Hom X Y → Type@{p}
  ; HomEq_Equivalence {X Y} :: Equivalence (@HomEq X Y)

  ; id {X} : Hom X X

  ; comp {X Y Z} : Hom Y Z → Hom X Y → Hom X Z

  ; comp_proper {X Y Z}
    :: Proper (@HomEq Y Z ==> @HomEq X Y ==> @HomEq X Z) comp

  ; comp_id_r {X Y : Ob} (f : Hom X Y)
    : HomEq (comp f id) f

  ; comp_id_l {X Y : Ob} (f : Hom X Y)
    : HomEq (comp id f) f

  ; comp_assoc {X Y Z W}
      (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y)
    : HomEq (comp (comp f g) h) (comp f (comp g h))
  }.

Arguments HomEq {_ _%_ob _%_ob} _%_hom _%_hom.
Arguments comp_id_l {_ _ _} _.
Arguments comp_id_r {_ _ _} _.
Arguments comp_assoc {_ _ _ _ _} _ _ _.

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

Ltac rw_assoc_r args := rewrite (comp_assoc args); cato.
Ltac rw_assoc_l args := rewrite <- (comp_assoc args); cato.

Tactic Notation "cacr" := rewrite comp_assoc; cato.
Tactic Notation "cacr" constr(t) := rw_assoc_r t.
Tactic Notation "cacl" := rewrite <- comp_assoc; cato.
Tactic Notation "cacl" constr(t) := rw_assoc_l t.

Hint Resolve comp_id_l : cat.
Hint Resolve comp_id_r : cat.

Hint Rewrite @comp_id_l : cat.
Hint Rewrite @comp_id_r : cat.



Section CatBasic.
Context `{Cat} {X Y : Ob}.

Theorem symm_id_l {x : Hom X Y} : x ≈ id ∘ x.
Proof. symmetry. cato. Qed.

Theorem symm_id_r {x : Hom X Y} : x ≈ x ∘ id.
Proof. symmetry. cato. Qed.

End CatBasic.

Hint Resolve symm_id_l : cat.
Hint Resolve symm_id_r : cat.



(** ** Morphisms induced by object equality

    These are transported identities. Their laws use equality elimination,
    without identifying distinct equality witnesses. *)

Definition eq_to_hom {C : Cat} {X Y : @Ob C} (p : X = Y) : Hom X Y :=
  match p with eq_refl => id end.

Lemma eq_to_hom_comp {C : Cat} {X Y Z : @Ob C} (p : X = Y) (q : Y = Z)
  : eq_to_hom (eq_trans p q) ≈ eq_to_hom q ∘ eq_to_hom p.
Proof. destruct p, q. simpl. symmetry. apply comp_id_l. Qed.

Lemma eq_to_hom_inv_l {C : Cat} {X Y : @Ob C} (p : X = Y)
  : eq_to_hom (eq_sym p) ∘ eq_to_hom p ≈ id.
Proof. destruct p. simpl. apply comp_id_l. Qed.

Lemma eq_to_hom_inv_r {C : Cat} {X Y : @Ob C} (p : X = Y)
  : eq_to_hom p ∘ eq_to_hom (eq_sym p) ≈ id.
Proof. destruct p. simpl. apply comp_id_l. Qed.



Definition comp_pre `{C : Cat} {X Y Z : Ob} (f : Hom X Y)
  := (λ g : Hom Y Z, g ∘ f).

Definition comp_post `{C : Cat} {X Y Z : Ob} (f : Hom Y Z)
  := (λ g : Hom X Y, f ∘ g).

Arguments comp_pre {_ _ _ _} _ _ /.
Arguments comp_post {_ _ _ _} _ _ /.

Notation "f ^*" := (comp_pre f) (at level 35).
Notation "f _*" := (comp_post f) (at level 35).



(** ** Dual Category *)

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
  symmetry. apply comp_assoc.
Qed.

Notation "C '^op'" := (op C)
  (at level 60).

Definition ob_op {C : Cat} (X : @Ob C) : (@Ob (C ^op))
  := X.

(* Coercion ob_op : Ob >-> Ob. *)



(** ** Prod Category *)

Program Definition ProdCat (C D : Cat) : Cat :=
  {|Ob := @Ob C * @Ob D
  ; Hom X Y := Hom (fst X) (fst Y) * Hom (snd X) (snd Y)
  ; HomEq X Y := ProdEq HomEq HomEq
  ; id _ := (id, id)
  ; comp _ _ _ f g := (fst f ∘ fst g, snd f ∘ snd g)
  |}.
Next Obligation. intros [fc fd] [gc gd] [H1c H1d].
  intros [hc hd] [jc jd] [H2c H2d]. split; simpl.
  rewrite H1c, H2c. reflexivity. rewrite H2d, H1d. reflexivity.
Qed.
Next Obligation. simpl. split; cato. Qed.
Next Obligation. simpl. split; cato. Qed.
Next Obligation. simpl. split; try cacr; reflexivity. Qed.

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

Definition is_linv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := g ∘ f ≈ id.

Definition is_rinv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := f ∘ g ≈ id.

Definition is_inv_of {X Y} (f : Hom X Y) (g : Hom Y X)
  := is_linv_of f g ∧ is_rinv_of f g.

Definition is_iso {X Y} (f : Hom X Y)
  := ∃ g, is_inv_of f g.

Definition iso X Y
  := ∃ f : Hom X Y, is_iso f.

Theorem is_inv_of_comm {X Y} (f : Hom X Y) (g : Hom Y X)
  : is_inv_of f g → is_inv_of g f.
Proof. intros [H1 H2]. split; auto. Qed.

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

Notation "f '⦂' X '≅' Y" := (@is_iso _ X Y f)
  (at level 50, no associativity,
    X at level 49, Y at level 49).

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
  - rewrite comp_assoc.
    rewrite <- (comp_assoc gi).
    rewrite Hg, comp_id_l. auto.
  - rewrite comp_assoc.
    rewrite <- (comp_assoc f).
    rewrite Hfi, comp_id_l. auto.
Qed.

Global Instance iso_Equivalence : Equivalence iso.
Proof.
  split.
  - intros x. apply iso_refl.
  - intros x y. apply iso_symm.
  - intros x y z. apply iso_trans.
Qed.

End Iso.



(** ** Terminal Objects *)

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



(** ** Product Objects *)

Definition is_product {C : Cat} (X Y P : Ob)
    (p : Hom P X) (q : Hom P Y) :=
  ∀ Z (f : Hom Z X) (g : Hom Z Y),
    ∃ h : Hom Z P, is_unique (λ h, p ∘ h ≈ f ∧ q ∘ h ≈ g) h.

Class HasProduct `(Cat) :=
  { Prod : Ob → Ob → Ob
  ; π1 {X Y} : Hom (Prod X Y) X
  ; π2 {X Y} : Hom (Prod X Y) Y

  ; product_universal {X Y} : is_product X Y (Prod X Y) π1 π2
  }.

Arguments Prod {_ _} _%_ob _%_ob.
Arguments π1 {_ _ _ _}.
Arguments π2 {_ _ _ _}.
Arguments product_universal {_ _ _ _} _ _ _.

(** The Type-valued universal property supplies the chosen mediator. *)
Definition pair {C : Cat} `{!HasProduct C} {X Y Z}
    (f : Hom Z X) (g : Hom Z Y) : Hom Z (Prod X Y) :=
  (product_universal Z f g).1.

Arguments pair {_ _ _ _ _} _ _.

Theorem product_pair_unique {C : Cat} `{!HasProduct C} {X Y Z}
    {f : Hom Z X} {g : Hom Z Y}
  : is_unique (λ h, π1 ∘ h ≈ f ∧ π2 ∘ h ≈ g) (pair f g).
Proof. exact (product_universal Z f g).2. Qed.

Arguments product_pair_unique {_ _ _ _} _ _ _.

Global Instance product_pair_proper {C : Cat} `{!HasProduct C} {X Y Z}
  : Proper (@HomEq[Z,X] ==> @HomEq[Z,Y] ==> @HomEq[Z,Prod X Y]) pair.
Proof.
  intros f f' Hf g g' Hg.
  destruct (product_pair_unique Z f g) as [[H1 H2] _].
  apply (product_pair_unique Z f' g'). split.
  - transitivity f; assumption.
  - transitivity g; assumption.
Qed.

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

Tactic Notation "elim_product" constr(H) "as" ident(h) :=
  let Hh1 := fresh "H" h "1" in
  let Hh2 := fresh "H" h "2" in
  let Hh_unique := fresh "H" h "_unique" in
  destruct H as (h & (Hh1 & Hh2) & Hh_unique).

Context {X Y P Q : Ob}.
Context {p1 : Hom P X} {p2 : Hom P Y}.
Context {q1 : Hom Q X} {q2 : Hom Q Y}.

Theorem product_unique
  : is_product X Y P p1 p2
  → is_product X Y Q q1 q2
  → P ≅ Q.
Proof.
  intros HP HQ.
  destruct (HP Q q1 q2) as [f [[Hf1 Hf2] Hf_unique]].
  destruct (HQ P p1 p2) as [g [[Hg1 Hg2] Hg_unique]].
  exists g, f; split; simpl.
  - destruct (HP P p1 p2) as [h [_ Hh_unique]].
    assert (Hid : id ≈ h).
    { apply Hh_unique; split; rewrite comp_id_r; reflexivity. }
    rewrite Hid. apply Hh_unique; split; rewrite <- comp_assoc.
    + rewrite Hf1, Hg1. reflexivity.
    + rewrite Hf2, Hg2. reflexivity.
  - destruct (HQ Q q1 q2) as [h [_ Hh_unique]].
    assert (Hid : id ≈ h).
    { apply Hh_unique; split; rewrite comp_id_r; reflexivity. }
    rewrite Hid. apply Hh_unique; split; rewrite <- comp_assoc.
    + rewrite Hg1, Hf1. reflexivity.
    + rewrite Hg2, Hf2. reflexivity.
Qed.

End Product.

Notation "P '⦂' '≅' X '×' Y 'with' p1 ',' p2"
  := (is_product X Y P p1 p2)
  (at level 50).



Section Product.
Context `{C : Cat} `{!HasProduct C}.

Proposition product_β1 {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : π1 ∘ ⟨f,g⟩ ≈ f.
Proof.
  pose (AP := product_pair_unique Z f g).
  destruct AP as [[H1 _] _].
  auto.
Qed.

Proposition product_β2 {X Y Z}
    (f : Hom Z X) (g : Hom Z Y)
  : π2 ∘ ⟨f,g⟩ ≈ g.
Proof.
  pose (AP := product_pair_unique Z f g).
  destruct AP as [[_ H2] _].
  auto.
Qed.

Lemma product_comp_r {X Y Z W}
    (f : Hom Z X) (g : Hom Z Y) (h : Hom W Z)
  : ⟨f , g⟩ ∘ h ≈ ⟨f ∘ h , g ∘ h⟩.
Proof.
  apply product_pair_unique.
  split.
  - rewrite <- comp_assoc, product_β1. cato.
  - rewrite <- comp_assoc, product_β2. cato.
Qed.

Lemma product_η {X Y Z} (h : Hom Z (X × Y))
  : h ≈ ⟨ π1 ∘ h , π2 ∘ h ⟩.
Proof.
  apply product_pair_unique; split; cato.
Qed.

Lemma product_comm {X Y} : X × Y ≅ Y × X.
Proof.
  exists ⟨π2, π1⟩, ⟨π2, π1⟩.
  simpl. split.
  - rewrite product_comp_r.
    rewrite product_β1.
    rewrite product_β2.
    symmetry.
    apply product_pair_unique.
    split; cato.
  - rewrite product_comp_r.
    rewrite product_β1.
    rewrite product_β2.
    symmetry.
    apply product_pair_unique.
    split; cato.
Qed.

End Product.

Hint Resolve product_universal : cat.
Hint Resolve product_β1 : cat.
Hint Resolve product_β2 : cat.

Hint Rewrite @product_β1 : cat.
Hint Rewrite @product_β2 : cat.



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

Lemma product_comp_l {X Y X' Y' Z}
    (f : Hom Z X) (g : Hom Z Y) (f' : Hom X X') (g' : Hom Y Y')
  : (f' × g') ∘ ⟨f , g⟩ ≈ ⟨f' ∘ f , g' ∘ g⟩.
Proof.
  apply product_pair_unique.
  split.
  - rewrite <- comp_assoc.
    rewrite cross_η.
    rewrite product_β1.
    rewrite comp_assoc.
    rewrite product_β1.
    cato.
  - rewrite <- comp_assoc.
    rewrite cross_η.
    rewrite product_β2.
    rewrite comp_assoc.
    rewrite product_β2.
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
  - rewrite product_comp_r.
    rewrite term_η.
    rewrite comp_id_l.
    symmetry.
    apply product_pair_unique.
    split; cato.
  - cato.
Qed.

Theorem term_prod_id_r {X}
  : X × 1 ≅ X.
Proof.
  rewrite product_comm.
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



(** ** Exponential Objects *)

Definition is_exponential {C : Cat} `{!HasProduct C}
    (X Y E : Ob) (ev : Hom (E × X) Y) :=
  ∀ Z (f : Hom (Z × X) Y),
    ∃ h : Hom Z E, is_unique (λ h, ev ∘ (h × id) ≈ f) h.

Class HasExponential {C : Cat} `(!HasProduct C) :=
  { exp : Ob → Ob → Ob
  ; eval {X Y} : Hom (exp Y X × X) Y

  ; exponential_universal {X Y} : is_exponential X Y (exp Y X) eval
  }.

Arguments exponential_universal {_ _ _ _ _} _ _.

Definition curry {C : Cat} `{HP : !HasProduct C} `{!HasExponential HP}
    {X Y Z} (f : Hom (Z × X) Y) : Hom Z (exp Y X) :=
  (exponential_universal Z f).1.

Theorem exponential_curry_unique {C : Cat}
    `{HP : !HasProduct C} `{!HasExponential HP} {X Y Z}
    (f : Hom (Z × X) Y)
  : is_unique (λ h, eval ∘ (h × id) ≈ f) (curry f).
Proof. exact (exponential_universal Z f).2. Qed.

Global Instance exponential_curry_proper {C : Cat}
    `{HP : !HasProduct C} `{!HasExponential HP} {X Y Z}
  : Proper (@HomEq[Z × X, Y] ==> @HomEq[Z, exp Y X]) curry.
Proof.
  intros f g Hfg.
  destruct (exponential_curry_unique f) as [Hf _].
  apply (exponential_curry_unique g). transitivity f; assumption.
Qed.

Notation "X '^' Y" := (exp X Y)
  (at level 30, right associativity): ob_scope.

Notation "'ƛ' f" := (curry f)
  (at level 35) : hom_scope.

Notation "'@eval' X Y" := (@eval _ _ _ _ X Y)
  (at level 35) : hom_scope.
