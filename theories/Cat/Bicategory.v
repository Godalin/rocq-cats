From Cats Require Import Cat.Core Cat.Functor.

Declare Scope bicat_scope.
Delimit Scope bicat_scope with bicat.
Local Open Scope bicat_scope.

(** * Bicategories

    Objects, hom-categories, composition and coherence form one structure.
    The intermediate operations are derived fields, not additional choices.
    The current [Functor]/[ProdCat] interfaces require 2-cells and their
    equivalence witnesses to share a universe; that restriction is inherited.
    No equality of 1-cells is implicit in this structure. *)

Class Bicat :=
  { ObB : Type
  ; HomCat : ObB → ObB → Cat
  ; id1 (X : ObB) : @Ob (HomCat X X)
  ; comp1F (X Y Z : ObB) : Functor (HomCat Y Z ×C HomCat X Y) (HomCat X Z)

  ; Cell1 (X Y : ObB) := @Ob (HomCat X Y)
  ; Cell2 {X Y : ObB} (f g : Cell1 X Y) := (@Hom (HomCat X Y)) f g
  ; CellEq {X Y} {f g : Cell1 X Y} (α β : Cell2 f g)
      := @Cats.Cat.Core.HomEq (HomCat X Y) f g α β
  ; comp1 {X Y Z} (g : Cell1 Y Z) (f : Cell1 X Y) : Cell1 X Z
      := comp1F X Y Z (g, f)
  ; id2 {X Y} (f : Cell1 X Y) : Cell2 f f := id
  ; comp2_v {X Y} {f g h : Cell1 X Y} (β : Cell2 g h) (α : Cell2 f g)
      : Cell2 f h := β ∘ α
  ; comp2_h {X Y Z} {g g' : Cell1 Y Z} {f f' : Cell1 X Y}
      (β : Cell2 g g') (α : Cell2 f f') : Cell2 (comp1 g f) (comp1 g' f')
      := fmap (comp1F X Y Z) (X := (g, f)) (Y := (g', f')) (β, α)

  ; associator {W X Y Z : ObB} (h : Cell1 Y Z) (g : Cell1 X Y) (f : Cell1 W X)
      : Cell2 (comp1 (comp1 h g) f) (comp1 h (comp1 g f))
  ; associator_iso {W X Y Z} (h : Cell1 Y Z) (g : Cell1 X Y) (f : Cell1 W X)
      : is_iso (associator h g f)
  ; left_unitor {X Y : ObB} (f : Cell1 X Y) : Cell2 (comp1 (id1 Y) f) f
  ; left_unitor_iso {X Y} (f : Cell1 X Y) : is_iso (left_unitor f)
  ; right_unitor {X Y : ObB} (f : Cell1 X Y) : Cell2 (comp1 f (id1 X)) f
  ; right_unitor_iso {X Y} (f : Cell1 X Y) : is_iso (right_unitor f)
  ; associator_naturality {W X Y Z} {h h' : Cell1 Y Z} {g g' : Cell1 X Y}
      {f f' : Cell1 W X} (γ : Cell2 h h') (β : Cell2 g g') (α : Cell2 f f')
      : CellEq (associator h' g' f' ∘ comp2_h (comp2_h γ β) α)
          (comp2_h γ (comp2_h β α) ∘ associator h g f)
  ; left_unitor_naturality {X Y} {f g : Cell1 X Y} (α : Cell2 f g)
      : CellEq (left_unitor g ∘ comp2_h (id2 (id1 Y)) α) (α ∘ left_unitor f)
  ; right_unitor_naturality {X Y} {f g : Cell1 X Y} (α : Cell2 f g)
      : CellEq (right_unitor g ∘ comp2_h α (id2 (id1 X))) (α ∘ right_unitor f)
  ; bicat_pentagon {V W X Y Z} (k : Cell1 Y Z) (h : Cell1 X Y)
      (g : Cell1 W X) (f : Cell1 V W)
      : CellEq (associator k h (comp1 g f) ∘ associator (comp1 k h) g f)
          (comp2_h (id2 k) (associator h g f) ∘
            (associator k (comp1 h g) f ∘ comp2_h (associator k h g) (id2 f)))
  ; bicat_triangle {X Y Z} (g : Cell1 Y Z) (f : Cell1 X Y)
      : CellEq (comp2_h (id2 g) (left_unitor f) ∘ associator g (id1 Y) f)
          (comp2_h (right_unitor g) (id2 f))
  }.

Arguments ObB _ : clear implicits.
Arguments HomCat {_} _ _.
Arguments id1 {_} _.
Arguments comp1F {_} _ _ _.
Arguments Cell1 {_} _ _.
Arguments Cell2 {_ _ _} _ _.
Arguments CellEq {_ _ _ _ _} _ _.
Arguments comp1 {_ _ _ _} _ _.
Arguments id2 {_ _ _} _.
Arguments comp2_v {_ _ _ _ _ _} _ _.
Arguments comp2_h {_ _ _ _ _ _ _ _} _ _.
Arguments associator {_ _ _ _ _} _ _ _.
Arguments left_unitor {_ _ _} _.
Arguments right_unitor {_ _ _} _.

Notation "f '⇒₂' g" := (Cell2 f g) (at level 50, no associativity) : bicat_scope.
Infix "≈₂" := CellEq (at level 50, no associativity) : bicat_scope.
Infix "∘₁" := comp1 (at level 40, left associativity) : bicat_scope.
Infix "∘₂" := comp2_v (at level 51, right associativity) : bicat_scope.
Infix "⋆" := comp2_h (at level 48, left associativity) : bicat_scope.
Notation "'𝟙₁' X" := (id1 X) (at level 35) : bicat_scope.
Notation "'𝟙₂' f" := (id2 f) (at level 35) : bicat_scope.

Global Instance CellEq_Equivalence {K : Bicat} {X Y : ObB K}
    {f g : Cell1 X Y} : Equivalence (@CellEq K X Y f g).
Proof. exact (@HomEq_Equivalence (HomCat X Y) f g). Qed.

Global Instance comp2_v_proper {K : Bicat} {X Y : ObB K}
    {f g h : Cell1 X Y}
  : Proper (CellEq ==> CellEq ==> CellEq) (@comp2_v K X Y f g h).
Proof. exact (@comp_proper (HomCat X Y) f g h). Qed.

Global Instance comp2_h_proper {K : Bicat} {X Y Z : ObB K}
    {g g' : Cell1 Y Z} {f f' : Cell1 X Y}
  : Proper (CellEq ==> CellEq ==> CellEq) (@comp2_h K X Y Z g g' f f').
Proof.
  intros β β' Hβ α α' Hα.
  exact (@functor_fmap_proper _ _ (comp1F X Y Z) (g, f) (g', f')
    (β, α) (β', α') (Hβ, Hα)).
Qed.

Theorem comp2_v_id_l {K : Bicat} {X Y : ObB K} {f g : Cell1 X Y}
    (α : f ⇒₂ g) : (𝟙₂ g ∘₂ α) ≈₂ α.
Proof. exact (comp_id_l α). Qed.

Theorem comp2_v_id_r {K : Bicat} {X Y : ObB K} {f g : Cell1 X Y}
    (α : f ⇒₂ g) : (α ∘₂ 𝟙₂ f) ≈₂ α.
Proof. exact (comp_id_r α). Qed.

Theorem comp2_v_assoc {K : Bicat} {X Y : ObB K} {f g h k : Cell1 X Y}
    (γ : h ⇒₂ k) (β : g ⇒₂ h) (α : f ⇒₂ g)
  : ((γ ∘₂ β) ∘₂ α) ≈₂ (γ ∘₂ (β ∘₂ α)).
Proof. exact (comp_assoc γ β α). Qed.

Theorem comp2_h_id {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) (f : Cell1 X Y)
  : (𝟙₂ g ⋆ 𝟙₂ f) ≈₂ 𝟙₂ (g ∘₁ f).
Proof. exact (@functor_id _ _ (comp1F X Y Z) (g, f)). Qed.

Theorem comp2_interchange {K : Bicat} {X Y Z : ObB K}
    {g0 g1 g2 : Cell1 Y Z} {f0 f1 f2 : Cell1 X Y}
    (β2 : g1 ⇒₂ g2) (β1 : g0 ⇒₂ g1) (α2 : f1 ⇒₂ f2) (α1 : f0 ⇒₂ f1)
  : ((β2 ∘₂ β1) ⋆ (α2 ∘₂ α1)) ≈₂ ((β2 ⋆ α2) ∘₂ (β1 ⋆ α1)).
Proof.
  exact (@functor_comp _ _ (comp1F X Y Z) (g0, f0) (g1, f1) (g2, f2)
    (β2, α2) (β1, α1)).
Qed.

Definition whisker_l {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) {f f' : Cell1 X Y} (α : f ⇒₂ f') := 𝟙₂ g ⋆ α.
Definition whisker_r {K : Bicat} {X Y Z : ObB K}
    {g g' : Cell1 Y Z} (β : g ⇒₂ g') (f : Cell1 X Y) := β ⋆ 𝟙₂ f.

Infix "◁" := whisker_l (at level 40, left associativity) : bicat_scope.
Infix "▷" := whisker_r (at level 40, left associativity) : bicat_scope.

Global Instance whisker_l_proper {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) {f f' : Cell1 X Y}
  : Proper (CellEq ==> CellEq) (@whisker_l K X Y Z g f f').
Proof. intros α β H. apply comp2_h_proper; [reflexivity | exact H]. Qed.

Global Instance whisker_r_proper {K : Bicat} {X Y Z : ObB K}
    {g g' : Cell1 Y Z} (f : Cell1 X Y)
  : Proper (CellEq ==> CellEq) (λ β : g ⇒₂ g', β ▷ f).
Proof. intros α β H. apply comp2_h_proper; [exact H | reflexivity]. Qed.

Theorem whisker_l_id {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) (f : Cell1 X Y) : (g ◁ 𝟙₂ f) ≈₂ 𝟙₂ (g ∘₁ f).
Proof. apply comp2_h_id. Qed.

Theorem whisker_r_id {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) (f : Cell1 X Y) : (𝟙₂ g ▷ f) ≈₂ 𝟙₂ (g ∘₁ f).
Proof. apply comp2_h_id. Qed.

Theorem whisker_l_comp {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) {f0 f1 f2 : Cell1 X Y} (β : f1 ⇒₂ f2) (α : f0 ⇒₂ f1)
  : (g ◁ (β ∘₂ α)) ≈₂ ((g ◁ β) ∘₂ (g ◁ α)).
Proof.
  transitivity ((𝟙₂ g ∘₂ 𝟙₂ g) ⋆ (β ∘₂ α)).
  - apply comp2_h_proper; [symmetry; apply comp2_v_id_l | reflexivity].
  - apply comp2_interchange.
Qed.

Theorem whisker_r_comp {K : Bicat} {X Y Z : ObB K}
    {g0 g1 g2 : Cell1 Y Z} (β : g1 ⇒₂ g2) (α : g0 ⇒₂ g1) (f : Cell1 X Y)
  : ((β ∘₂ α) ▷ f) ≈₂ ((β ▷ f) ∘₂ (α ▷ f)).
Proof.
  transitivity ((β ∘₂ α) ⋆ (𝟙₂ f ∘₂ 𝟙₂ f)).
  - apply comp2_h_proper; [reflexivity | symmetry; apply comp2_v_id_l].
  - apply comp2_interchange.
Qed.
