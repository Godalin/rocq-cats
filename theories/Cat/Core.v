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

(** Morphisms and their equivalence witnesses have independent sizes.
    Equivalence/properness laws may live in larger auxiliary universes. *)
Class Cat@{o h p +} :=
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
Next Obligation. apply comp_id_l. Qed.
Next Obligation. apply comp_id_r. Qed.
Next Obligation.
  symmetry. apply comp_assoc.
Qed.

Notation "C '^op'" := (op C)
  (at level 60).

Definition ob_op {C : Cat} (X : @Ob C) : (@Ob (C ^op))
  := X.

Lemma eq_to_hom_op {C : Cat} {X Y : @Ob C} (p : X = Y)
  : @eq_to_hom (C ^op) X Y p ≈ eq_to_hom (eq_sym p).
Proof. destruct p. reflexivity. Qed.



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
Next Obligation. destruct f. simpl. split; apply comp_id_r. Qed.
Next Obligation. destruct f. simpl. split; apply comp_id_l. Qed.
Next Obligation. destruct f, g, h. simpl. split; apply comp_assoc. Qed.

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
