From Cats Require Import Cat.Core Cat.Functor Cat.Natural.

(** * Diagrams, Constant Diagrams and Cones *)

Program Definition ConstF (J : Cat) {C : Cat} (X : @Ob C) : Functor J C :=
  {| F0 j := X; F1 j k f := id |}.
Next Obligation. intros f g H. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. symmetry. apply comp_id_l. Qed.

Program Definition DiagonalF (J C : Cat) : Functor C (Fct J C) :=
  {| F0 X := ConstF J X
   ; F1 X Y f := {| nt j := f |} |}.
Next Obligation. carw. Qed.
Next Obligation. intros f g H j. exact H. Qed.
Next Obligation. intros j. reflexivity. Qed.
Next Obligation. intros j. reflexivity. Qed.

Notation "'Δ[' J ',' C ']'" := (DiagonalF J C) : cat_scope.

Definition Cone {J C : Cat} (D : Functor J C) (X : @Ob C) := ConstF J X ⇒ D.
Notation "X '⇒Δ' D" := (Cone D X)
  (at level 50, no associativity) : cat_scope.

Lemma cone_naturality {J C : Cat} {D : Functor J C} {X}
    (κ : X ⇒Δ D) {i j : @Ob J} (f : Hom i j)
  : κ j ≈ fmap D f ∘ κ i.
Proof.
  pose proof (nt_naturality κ f) as H. cbn in H.
  rewrite comp_id_r in H. exact H.
Qed.

Definition cone_comp {J C : Cat} {D : Functor J C} {X Y : @Ob C}
    (κ : X ⇒Δ D) (f : Hom Y X) : Y ⇒Δ D :=
  κ ∘Nv fmap (DiagonalF J C) f.

Infix "∘Cone" := cone_comp (at level 40, left associativity) : cat_scope.

Global Instance cone_comp_proper {J C : Cat} {D : Functor J C} {X Y : @Ob C}
  : Proper (NatEq ==> @HomEq[Y, X] ==> NatEq) (@cone_comp J C D X Y).
Proof. intros κ μ H f g K j. cbn. rewrite (H j), K. reflexivity. Qed.

Lemma cone_comp_id {J C : Cat} {D : Functor J C} {X} (κ : X ⇒Δ D)
  : κ ∘Cone id ≈N κ.
Proof. intros j. apply comp_id_r. Qed.

Lemma cone_comp_assoc {J C : Cat} {D : Functor J C} {X Y Z}
    (κ : X ⇒Δ D) (f : Hom Y X) (g : Hom Z Y)
  : (κ ∘Cone f) ∘Cone g ≈N κ ∘Cone (f ∘ g).
Proof. intros j. apply comp_assoc. Qed.

Program Definition MapCone {J C E : Cat} (F : Functor C E)
    {D : Functor J C} {X : @Ob C} (κ : X ⇒Δ D) : F X ⇒Δ (F ∘F D) :=
  {| nt j := fmap F (κ j) |}.
Next Obligation.
  rewrite comp_id_r, <- (functor_comp C E F).
  apply functor_fmap_proper.
  pose proof (nt_naturality κ f) as H. cbn in H.
  rewrite comp_id_r in H. exact H.
Qed.

(** Cone morphisms compare the apex maps, retaining commutativity witnesses
    without comparing those witnesses. *)
Definition ConeOb {J C : Cat} (D : Functor J C) := ∃ X : @Ob C, X ⇒Δ D.
Definition ConeMap {J C : Cat} {D : Functor J C} (κ μ : ConeOb D) :=
  ∃ f : Hom κ.1 μ.1, μ.2 ∘Cone f ≈N κ.2.

Program Definition ConeCat {J C : Cat} (D : Functor J C) : Cat :=
  {| Ob := ConeOb D
   ; HomSet κ μ :=
       {| carrier := ConeMap κ μ
        ; carrier_equiv f g := f.1 ≈ g.1 |}
   ; id κ := (id; _)
   ; comp κ μ ν g f := (g.1 ∘ f.1; _) |}.
Next Obligation.
  split.
  - intros f. reflexivity.
  - intros f g H. symmetry. exact H.
  - intros f g h H K. transitivity g.1; assumption.
Defined.
Next Obligation. apply cone_comp_id. Defined.
Next Obligation.
  rewrite <- cone_comp_assoc, g.2, f.2. reflexivity.
Defined.
Next Obligation. intros f f' H g g' K. cbn in *. rewrite H, K. reflexivity. Qed.
Next Obligation. apply comp_id_r. Qed.
Next Obligation. apply comp_id_l. Qed.
Next Obligation. apply comp_assoc. Qed.

Program Definition ConeApexF {J C : Cat} (D : Functor J C)
  : Functor (ConeCat D) C :=
  {| F0 κ := κ.1; F1 κ μ f := f.1 |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
