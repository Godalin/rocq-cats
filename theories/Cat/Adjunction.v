From Cats Require Import Cat.Core Cat.Functor Cat.Natural.
From Cats Require Import Instance.Set.Core Instance.Set.Hom.

(** * Adjunctions by Natural Hom Isomorphisms

    Both hom-functors inherit their functor laws from HomF. The chosen
    natural isomorphism supplies forward naturality; inverse naturality is
    derived by NatIso_inv. The ambient set levels are independent upper
    bounds, not identifications of the two categories' native hom levels. *)

Class Adjunction@{u p +} {C D : Cat} (F : Functor C D) (G : Functor D C) :=
  { adjunction_hom : @NatIso _ SetCat@{u p _ _ _ _ _}
      (LeftHomF F) (RightHomF G) }.

Arguments adjunction_hom {_ _ _ _} _.
Infix "⊣" := Adjunction (at level 50, no associativity) : cat_scope.

Section Transposition.
Context {C D : Cat} {F : Functor C D} {G : Functor D C} (A : F ⊣ G).

Program Definition adjunct_resp@{s +} {X Y}
  : FunS_resp@{s _ _ _ _ _} (HomSet (F X) Y) (HomSet X (G Y)) :=
  {| func f := lower ((adjunction_hom A).1 (X, Y) {| lower := f |}) |}.
Next Obligation.
  intros f g H.
  exact (lower (@func_proper _ _ ((adjunction_hom A).1 (X, Y))
    {| lower := f |} {| lower := g |} {| lower := H |})).
Defined.

Program Definition unadjunct_resp@{s +} {X Y}
  : FunS_resp@{s _ _ _ _ _} (HomSet X (G Y)) (HomSet (F X) Y) :=
  {| func g := lower (((adjunction_hom A).2 (X, Y)).1 {| lower := g |}) |}.
Next Obligation.
  intros f g H.
  exact (lower (@func_proper _ _ ((adjunction_hom A).2 (X, Y)).1
    {| lower := f |} {| lower := g |} {| lower := H |})).
Defined.

Definition adjunct {X Y} (f : Hom (F X) Y) : Hom X (G Y) := adjunct_resp f.
Definition unadjunct {X Y} (g : Hom X (G Y)) : Hom (F X) Y := unadjunct_resp g.

Global Instance adjunct_proper {X Y}
  : Proper (@HomEq[F X, Y] ==> @HomEq[X, G Y]) adjunct.
Proof. apply func_proper. Qed.

Global Instance unadjunct_proper {X Y}
  : Proper (@HomEq[X, G Y] ==> @HomEq[F X, Y]) unadjunct.
Proof. apply func_proper. Qed.

Theorem adjunction_β {X Y} (f : Hom (F X) Y)
  : unadjunct (adjunct f) ≈ f.
Proof.
  pose proof (fst ((adjunction_hom A).2 (X, Y)).2 {| lower := f |}) as H.
  etransitivity.
  - exact (lower (@func_proper _ _ ((adjunction_hom A).2 (X, Y)).1
      {| lower := lower ((adjunction_hom A).1 (X, Y) {| lower := f |}) |}
      ((adjunction_hom A).1 (X, Y) {| lower := f |})
      {| lower := reflexivity _ |})).
  - exact (lower H).
Qed.

Theorem adjunction_η {X Y} (g : Hom X (G Y))
  : adjunct (unadjunct g) ≈ g.
Proof.
  pose proof (snd ((adjunction_hom A).2 (X, Y)).2 {| lower := g |}) as H.
  etransitivity.
  - exact (lower (@func_proper _ _ ((adjunction_hom A).1 (X, Y))
      {| lower := lower (((adjunction_hom A).2 (X, Y)).1 {| lower := g |}) |}
      (((adjunction_hom A).2 (X, Y)).1 {| lower := g |})
      {| lower := reflexivity _ |})).
  - exact (lower H).
Qed.

Lemma adjunct_naturality {X X' : @Ob C} {Y Y' : @Ob D}
    (h : Hom X' X) (k : Hom Y Y')
    (f : Hom (F X) Y)
  : adjunct (k ∘ f ∘ fmap F h) ≈ fmap G k ∘ adjunct f ∘ h.
Proof.
  exact (lower (nt_naturality (adjunction_hom A).1
    (X := (X, Y)) (Y := (X', Y')) (h, k) {| lower := f |})).
Qed.

Lemma adjunct_comp_r {X X' Y} (f : Hom (F X) Y) (h : Hom X' X)
  : adjunct (f ∘ fmap F h) ≈ adjunct f ∘ h.
Proof.
  pose proof (adjunct_naturality h id f) as H.
  rewrite (functor_id D C G), !comp_id_l in H. exact H.
Qed.

Lemma adjunct_comp_l {X Y Y'} (k : Hom Y Y') (f : Hom (F X) Y)
  : adjunct (k ∘ f) ≈ fmap G k ∘ adjunct f.
Proof.
  pose proof (adjunct_naturality id k f) as H.
  rewrite (functor_id C D F), !comp_id_r in H. exact H.
Qed.

Lemma unadjunct_naturality {X X' : @Ob C} {Y Y' : @Ob D}
    (h : Hom X' X) (k : Hom Y Y') (g : Hom X (G Y))
  : unadjunct (fmap G k ∘ g ∘ h) ≈ k ∘ unadjunct g ∘ fmap F h.
Proof.
  exact (lower (nt_naturality
    (NatIso_inv (adjunction_hom A).1 (adjunction_hom A).2)
    (X := (X, Y)) (Y := (X', Y')) (h, k) {| lower := g |})).
Qed.

Lemma unadjunct_comp_r {X X' Y} (g : Hom X (G Y)) (h : Hom X' X)
  : unadjunct (g ∘ h) ≈ unadjunct g ∘ fmap F h.
Proof.
  pose proof (unadjunct_naturality h id g) as H.
  rewrite (functor_id D C G), !comp_id_l in H. exact H.
Qed.

Lemma unadjunct_comp_l {X Y Y'} (k : Hom Y Y') (g : Hom X (G Y))
  : unadjunct (fmap G k ∘ g) ≈ k ∘ unadjunct g.
Proof.
  pose proof (unadjunct_naturality id k g) as H.
  rewrite (functor_id C D F), !comp_id_r in H. exact H.
Qed.

Theorem adjunct_iff {X Y} (f : Hom (F X) Y) (g : Hom X (G Y))
  : adjunct f ≈ g ↔ f ≈ unadjunct g.
Proof.
  split; intros H.
  - rewrite <- (adjunction_β f), H. reflexivity.
  - rewrite H, adjunction_η. reflexivity.
Qed.

(** Unit and counit are transposed identities, with naturality inherited
    from the hom correspondence. They are not additional chosen fields. *)
Program Definition adjunction_unit : IdF ⇒ G ∘F F :=
  {| nt X := adjunct id |}.
Next Obligation.
  rewrite <- (adjunct_comp_r id f), comp_id_l.
  rewrite <- (adjunct_comp_l (fmap F f) id), comp_id_r. reflexivity.
Qed.

Program Definition adjunction_counit : F ∘F G ⇒ IdF :=
  {| nt Y := unadjunct id |}.
Next Obligation.
  rewrite <- (unadjunct_comp_r (@id (G Y)) (fmap G f)), comp_id_l.
  rewrite <- (unadjunct_comp_l f (@id (G X))), comp_id_r. reflexivity.
Qed.

Lemma adjunct_unit {X Y} (f : Hom (F X) Y)
  : adjunct f ≈ fmap G f ∘ adjunction_unit X.
Proof.
  change (adjunct f ≈ fmap G f ∘ adjunct (@id (F X))).
  rewrite <- (adjunct_comp_l f (@id (F X))), comp_id_r. reflexivity.
Qed.

Lemma unadjunct_counit {X Y} (g : Hom X (G Y))
  : unadjunct g ≈ adjunction_counit Y ∘ fmap F g.
Proof.
  change (unadjunct g ≈ unadjunct (@id (G Y)) ∘ fmap F g).
  rewrite <- (unadjunct_comp_r (@id (G Y)) g), comp_id_l. reflexivity.
Qed.

Theorem adjunction_triangle_l (X : @Ob C)
  : adjunction_counit (F X) ∘ fmap F (adjunction_unit X) ≈ id.
Proof.
  transitivity (unadjunct (adjunct (@id (F X)))).
  - symmetry. apply unadjunct_counit.
  - apply adjunction_β.
Qed.

Theorem adjunction_triangle_r (Y : @Ob D)
  : fmap G (adjunction_counit Y) ∘ adjunction_unit (G Y) ≈ id.
Proof.
  transitivity (adjunct (unadjunct (@id (G Y)))).
  - symmetry. apply adjunct_unit.
  - apply adjunction_η.
Qed.

Theorem adjunction_unit_universal {X Y} (g : Hom X (G Y))
  : is_unique (λ f, fmap G f ∘ adjunction_unit X ≈ g) (unadjunct g).
Proof.
  refine {| this := _; that := _ |}.
  - rewrite <- adjunct_unit. apply adjunction_η.
  - intros f H. apply (fst (adjunct_iff f g)). rewrite adjunct_unit. exact H.
Defined.

Theorem adjunction_counit_universal {X Y} (f : Hom (F X) Y)
  : is_unique (λ g, adjunction_counit Y ∘ fmap F g ≈ f) (adjunct f).
Proof.
  refine {| this := _; that := _ |}.
  - rewrite <- unadjunct_counit. apply adjunction_β.
  - intros g H. symmetry. apply (snd (adjunct_iff f g)).
    rewrite unadjunct_counit. symmetry. exact H.
Defined.

End Transposition.

Notation "f '^♯[' A ']'" := (adjunct A f) (at level 35) : hom_scope.
Notation "g '^♭[' A ']'" := (unadjunct A g) (at level 35) : hom_scope.

(** ** Building the Natural Isomorphism from Native Hom Maps

    Only forward naturality needs to be supplied. The inverse laws are
    precisely the component isomorphism laws. *)
Section HomCorrespondence.
Context {C D : Cat} (F : Functor C D) (G : Functor D C).
Context (φ : ∀ X Y, HomSet (F X) Y →r HomSet X (G Y)).
Context (ψ : ∀ X Y, HomSet X (G Y) →r HomSet (F X) Y).
Context (hom_β : ∀ X Y f, ψ X Y (φ X Y f) ≈ f).
Context (hom_η : ∀ X Y g, φ X Y (ψ X Y g) ≈ g).
Context (hom_comp_r : ∀ X X' Y (f : Hom (F X) Y) (h : Hom X' X),
  φ X' Y (f ∘ fmap F h) ≈ φ X Y f ∘ h).
Context (hom_comp_l : ∀ X Y Y' (k : Hom Y Y') (f : Hom (F X) Y),
  φ X Y' (k ∘ f) ≈ fmap G k ∘ φ X Y f).

Program Definition HomAdjunctN : LeftHomF F ⇒ RightHomF G :=
  {| nt X := (φ (fst X) (snd X))^↑S |}.
Next Obligation.
  intros [h]. constructor.
  change (φ (fst Y) (snd Y) (snd f ∘ h ∘ fmap F (fst f)) ≈
    fmap G (snd f) ∘ φ (fst X) (snd X) h ∘ fst f).
  rewrite hom_comp_r, hom_comp_l. reflexivity.
Defined.

Definition AdjunctionFromHom : F ⊣ G.
Proof.
  refine {| adjunction_hom := (HomAdjunctN; _) |}.
  intros [X Y]. exists ((ψ X Y)^↑S). split; intros [f]; constructor;
    [apply hom_β | apply hom_η].
Defined.

Theorem adjunct_from_hom {X Y} (f : Hom (F X) Y)
  : f^♯[AdjunctionFromHom] ≈ φ X Y f.
Proof. reflexivity. Qed.

Theorem unadjunct_from_hom {X Y} (g : Hom X (G Y))
  : g^♭[AdjunctionFromHom] ≈ ψ X Y g.
Proof. reflexivity. Qed.

End HomCorrespondence.

Definition IdAdjunction (C : Cat) : (@IdF C) ⊣ IdF.
Proof.
  refine (AdjunctionFromHom IdF IdF (λ X Y, id_resp) (λ X Y, id_resp) _ _ _ _);
    intros; reflexivity.
Defined.

Definition CompAdjunction {C D E : Cat}
    {F : Functor C D} {G : Functor D C}
    {L : Functor D E} {R : Functor E D} (B : L ⊣ R) (A : F ⊣ G)
  : (L ∘F F) ⊣ (G ∘F R).
Proof.
  refine (AdjunctionFromHom (L ∘F F) (G ∘F R)
    (λ X Y, adjunct_resp A ∘r adjunct_resp B)
    (λ X Y, unadjunct_resp B ∘r unadjunct_resp A) _ _ _ _).
  - intros X Y f.
    change (unadjunct B (unadjunct A (adjunct A (adjunct B f))) ≈ f).
    rewrite (adjunction_β A), (adjunction_β B). reflexivity.
  - intros X Y g.
    change (adjunct A (adjunct B (unadjunct B (unadjunct A g))) ≈ g).
    rewrite (adjunction_η B), (adjunction_η A). reflexivity.
  - intros X X' Y f h.
    change (adjunct A (adjunct B (f ∘ fmap L (fmap F h))) ≈
      adjunct A (adjunct B f) ∘ h).
    rewrite (adjunct_comp_r B f (fmap F h)), (adjunct_comp_r A (adjunct B f) h).
    reflexivity.
  - intros X Y Y' k f.
    change (adjunct A (adjunct B (k ∘ f)) ≈
      fmap G (fmap R k) ∘ adjunct A (adjunct B f)).
    rewrite (adjunct_comp_l B k f), (adjunct_comp_l A (fmap R k) (adjunct B f)).
    reflexivity.
Defined.
