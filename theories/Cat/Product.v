From Cats Require Import Cat.Core Cat.Terminal.

(** * Product Objects *)

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
