From Cats Require Import
  Cat.Core
  Cat.Functor.Core.

Declare Scope bicat_scope.
Delimit Scope bicat_scope with bicat.
Local Open Scope bicat_scope.

Reserved Notation "f ⇒₂ g" (at level 50, no associativity).
Reserved Notation "α ≈₂ β" (at level 50, no associativity).
Reserved Notation "g ∘₁ f" (at level 40, left associativity).
Reserved Notation "β ∘₂ α" (at level 51, right associativity).
Reserved Notation "β ⋆ α" (at level 48, left associativity).
Reserved Notation "'𝟙₁' X" (at level 35).
Reserved Notation "'𝟙₂' f" (at level 35).

(** * Bicategories

    Objects, hom-categories, composition and coherence form one structure. The
    intermediate operations are derived fields, not additional choices. The
    four named universes are for 0-cells, 1-cells, 2-cells and their
    equivalence witnesses. Law witnesses use auxiliary upper-bound universes.
    No equality of 1-cells is implicit in this structure. *)

(** * 双范畴

    对象、Hom 范畴、复合与相干律组成一个结构；中间运算是派生字段，不是额外选择。
    四个指定宇宙分别容纳零胞、一胞、二胞及其等价见证，定律使用辅助上界宇宙。此
    结构不隐含一胞相等。 *)

Class Bicat@{o h t p +}
  :=
  { ObB : Type@{o}
  ; HomCat : ObB → ObB → Cat@{h t p _ _}
  ; id1 (X : ObB) : @Ob (HomCat X X)
    where "'𝟙₁' X" := (id1 X) : bicat_scope
  ; comp1F (X Y Z : ObB) : Functor (HomCat Y Z ×C HomCat X Y) (HomCat X Z)

  ; Cell1 (X Y : ObB) := @Ob (HomCat X Y)
  ; Cell2 {X Y : ObB} (f g : Cell1 X Y) := (@Hom (HomCat X Y)) f g
    where "f ⇒₂ g" := (Cell2 f g) : bicat_scope
  ; Cell2Eq {X Y} {f g : Cell1 X Y} (α β : f ⇒₂ g)
  := @Cats.Cat.Core.HomEq (HomCat X Y) f g α β
    where "α ≈₂ β" := (Cell2Eq α β) : bicat_scope
  ; comp1 {X Y Z} (g : Cell1 Y Z) (f : Cell1 X Y) : Cell1 X Z
  := comp1F X Y Z (g, f)
    where "g ∘₁ f" := (comp1 g f) : bicat_scope
  ; id2 {X Y} (f : Cell1 X Y) : f ⇒₂ f := id
    where "'𝟙₂' f" := (id2 f) : bicat_scope
  ; comp2_v {X Y} {f g h : Cell1 X Y} (β : g ⇒₂ h) (α : f ⇒₂ g)
      : f ⇒₂ h := β ∘ α
    where "β ∘₂ α" := (comp2_v β α) : bicat_scope
  ; comp2_h {X Y Z} {g g' : Cell1 Y Z} {f f' : Cell1 X Y}
      (β : g ⇒₂ g') (α : f ⇒₂ f') : (g ∘₁ f) ⇒₂ (g' ∘₁ f')
  := fmap (comp1F X Y Z) (X := (g, f)) (Y := (g', f')) (β, α)
    where "β ⋆ α" := (comp2_h β α) : bicat_scope

  ; associator {W X Y Z : ObB} (h : Cell1 Y Z) (g : Cell1 X Y) (f : Cell1 W X)
      : ((h ∘₁ g) ∘₁ f) ⇒₂ (h ∘₁ (g ∘₁ f))
  ; associator_iso {W X Y Z} (h : Cell1 Y Z) (g : Cell1 X Y) (f : Cell1 W X)
      : is_iso (associator h g f)
  ; left_unitor {X Y : ObB} (f : Cell1 X Y) : (𝟙₁ Y ∘₁ f) ⇒₂ f
  ; left_unitor_iso {X Y} (f : Cell1 X Y) : is_iso (left_unitor f)
  ; right_unitor {X Y : ObB} (f : Cell1 X Y) : (f ∘₁ 𝟙₁ X) ⇒₂ f
  ; right_unitor_iso {X Y} (f : Cell1 X Y) : is_iso (right_unitor f)
  ; associator_naturality {W X Y Z} {h h' : Cell1 Y Z} {g g' : Cell1 X Y}
      {f f' : Cell1 W X} (γ : h ⇒₂ h') (β : g ⇒₂ g') (α : f ⇒₂ f')
      : (associator h' g' f' ∘₂ ((γ ⋆ β) ⋆ α)) ≈₂
          ((γ ⋆ (β ⋆ α)) ∘₂ associator h g f)
  ; left_unitor_naturality {X Y} {f g : Cell1 X Y} (α : f ⇒₂ g)
      : (left_unitor g ∘₂ (𝟙₂ (𝟙₁ Y) ⋆ α)) ≈₂ (α ∘₂ left_unitor f)
  ; right_unitor_naturality {X Y} {f g : Cell1 X Y} (α : f ⇒₂ g)
      : (right_unitor g ∘₂ (α ⋆ 𝟙₂ (𝟙₁ X))) ≈₂ (α ∘₂ right_unitor f)
  ; bicat_pentagon {V W X Y Z} (k : Cell1 Y Z) (h : Cell1 X Y)
      (g : Cell1 W X) (f : Cell1 V W)
      : (associator k h (g ∘₁ f) ∘₂ associator (k ∘₁ h) g f) ≈₂
          ((𝟙₂ k ⋆ associator h g f) ∘₂
            (associator k (h ∘₁ g) f ∘₂ (associator k h g ⋆ 𝟙₂ f)))
  ; bicat_triangle {X Y Z} (g : Cell1 Y Z) (f : Cell1 X Y)
      : ((𝟙₂ g ⋆ left_unitor f) ∘₂ associator g (𝟙₁ Y) f) ≈₂
          right_unitor g ⋆ 𝟙₂ f
  }.

Arguments ObB _ : clear implicits.
Arguments HomCat {_} _ _.
Arguments id1 {_} _.
Arguments comp1F {_} _ _ _.
Arguments Cell1 {_} _ _.
Arguments Cell2 {_ _ _} _ _.
Arguments Cell2Eq {_ _ _ _ _} _ _.
Arguments comp1 {_ _ _ _} _ _.
Arguments id2 {_ _ _} _.
Arguments comp2_v {_ _ _ _ _ _} _ _.
Arguments comp2_h {_ _ _ _ _ _ _ _} _ _.
Arguments associator {_ _ _ _ _} _ _ _.
Arguments left_unitor {_ _ _} _.
Arguments right_unitor {_ _ _} _.

Notation "f '⇒₂' g" := (Cell2 f g) (at level 50, no associativity) : bicat_scope.
Infix "≈₂" := Cell2Eq (at level 50, no associativity) : bicat_scope.
Infix "∘₁" := comp1 (at level 40, left associativity) : bicat_scope.
Infix "∘₂" := comp2_v (at level 51, right associativity) : bicat_scope.
Infix "⋆" := comp2_h (at level 48, left associativity) : bicat_scope.
Notation "'𝟙₁' X" := (id1 X) (at level 35) : bicat_scope.
Notation "'𝟙₂' f" := (id2 f) (at level 35) : bicat_scope.

(** [Cell2Eq] is an equivalence relation. *)

(** [Cell2Eq] 是等价关系。 *)

Global Instance Cell2Eq_Equivalence {K : Bicat} {X Y : ObB K}
    {f g : Cell1 X Y}
  : Equivalence (@Cell2Eq K X Y f g).
Proof. exact (@HomEq_Equivalence (HomCat X Y) f g). Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance comp2_v_proper {K : Bicat} {X Y : ObB K}
    {f g h : Cell1 X Y}
  : Proper (Cell2Eq ==> Cell2Eq ==> Cell2Eq) (@comp2_v K X Y f g h).
Proof. exact (@comp_proper (HomCat X Y) f g h). Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance comp2_h_proper {K : Bicat} {X Y Z : ObB K}
    {g g' : Cell1 Y Z} {f f' : Cell1 X Y}
  : Proper (Cell2Eq ==> Cell2Eq ==> Cell2Eq) (@comp2_h K X Y Z g g' f f').
Proof.
  intros β β' Hβ α α' Hα.
  exact (@functor_fmap_proper _ _ (comp1F X Y Z) (g, f) (g', f')
    (β, α) (β', α') (Hβ, Hα)).
Qed.

(** An identity two-cell is a left unit for vertical composition. *)

(** 恒等二胞是垂直复合的左单位。 *)

Theorem comp2_v_id_l {K : Bicat} {X Y : ObB K} {f g : Cell1 X Y}
    (α : f ⇒₂ g)
  : (𝟙₂ g ∘₂ α) ≈₂ α.
Proof. exact (comp_id_l α). Qed.

(** An identity two-cell is a right unit for vertical composition. *)

(** 恒等二胞是垂直复合的右单位。 *)

Theorem comp2_v_id_r {K : Bicat} {X Y : ObB K} {f g : Cell1 X Y}
    (α : f ⇒₂ g)
  : (α ∘₂ 𝟙₂ f) ≈₂ α.
Proof. exact (comp_id_r α). Qed.

(** Vertical composition of two-cells is associative. *)

(** 二胞的垂直复合满足结合律。 *)

Theorem comp2_v_assoc {K : Bicat} {X Y : ObB K} {f g h k : Cell1 X Y}
    (γ : h ⇒₂ k) (β : g ⇒₂ h) (α : f ⇒₂ g)
  : ((γ ∘₂ β) ∘₂ α) ≈₂ (γ ∘₂ (β ∘₂ α)).
Proof. exact (comp_assoc γ β α). Qed.

(** Horizontal composition of identity two-cells is the composite's identity. *)

(** 恒等二胞的水平复合是复合一胞的恒等二胞。 *)

Theorem comp2_h_id {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) (f : Cell1 X Y)
  : (𝟙₂ g ⋆ 𝟙₂ f) ≈₂ 𝟙₂ (g ∘₁ f).
Proof. exact (@functor_id _ _ (comp1F X Y Z) (g, f)). Qed.

(** Horizontal composition commutes with vertical composition of two-cell
    pairs. *)

(** 水平复合与二胞对的垂直复合交换。 *)

Theorem comp2_interchange {K : Bicat} {X Y Z : ObB K}
    {g0 g1 g2 : Cell1 Y Z} {f0 f1 f2 : Cell1 X Y}
    (β2 : g1 ⇒₂ g2) (β1 : g0 ⇒₂ g1) (α2 : f1 ⇒₂ f2) (α1 : f0 ⇒₂ f1)
  : ((β2 ∘₂ β1) ⋆ (α2 ∘₂ α1)) ≈₂ ((β2 ⋆ α2) ∘₂ (β1 ⋆ α1)).
Proof.
  exact (@functor_comp _ _ (comp1F X Y Z) (g0, f0) (g1, f1) (g2, f2)
    (β2, α2) (β1, α1)).
Qed.

(** Compose a two-cell horizontally with the identity on a fixed left
    one-cell. *)

(** 将二胞与固定左侧一胞的恒等二胞水平复合。 *)

Definition whisker_l {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) {f f' : Cell1 X Y} (α : f ⇒₂ f')
  := 𝟙₂ g ⋆ α.
(** Compose a two-cell horizontally with the identity on a fixed right
    one-cell. *)

(** 将二胞与固定右侧一胞的恒等二胞水平复合。 *)

Definition whisker_r {K : Bicat} {X Y Z : ObB K}
    {g g' : Cell1 Y Z} (β : g ⇒₂ g') (f : Cell1 X Y)
  := β ⋆ 𝟙₂ f.

Infix "◁" := whisker_l (at level 40, left associativity) : bicat_scope.
Infix "▷" := whisker_r (at level 40, left associativity) : bicat_scope.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance whisker_l_proper {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) {f f' : Cell1 X Y}
  : Proper (Cell2Eq ==> Cell2Eq) (@whisker_l K X Y Z g f f').
Proof. intros α β H. apply comp2_h_proper; [reflexivity | exact H]. Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance whisker_r_proper {K : Bicat} {X Y Z : ObB K}
    {g g' : Cell1 Y Z} (f : Cell1 X Y)
  : Proper (Cell2Eq ==> Cell2Eq) (λ β : g ⇒₂ g', β ▷ f).
Proof. intros α β H. apply comp2_h_proper; [exact H | reflexivity]. Qed.

(** Compatibility with identities for [whisker_l]. *)

(** [whisker_l] 与恒等的相容性。 *)

Theorem whisker_l_id {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) (f : Cell1 X Y)
  : (g ◁ 𝟙₂ f) ≈₂ 𝟙₂ (g ∘₁ f).
Proof. apply comp2_h_id. Qed.

(** Compatibility with identities for [whisker_r]. *)

(** [whisker_r] 与恒等的相容性。 *)

Theorem whisker_r_id {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) (f : Cell1 X Y)
  : (𝟙₂ g ▷ f) ≈₂ 𝟙₂ (g ∘₁ f).
Proof. apply comp2_h_id. Qed.

(** Compatibility with composition for [whisker_l]. *)

(** [whisker_l] 与复合的相容性。 *)

Theorem whisker_l_comp {K : Bicat} {X Y Z : ObB K}
    (g : Cell1 Y Z) {f0 f1 f2 : Cell1 X Y} (β : f1 ⇒₂ f2) (α : f0 ⇒₂ f1)
  : (g ◁ (β ∘₂ α)) ≈₂ ((g ◁ β) ∘₂ (g ◁ α)).
Proof.
  transitivity ((𝟙₂ g ∘₂ 𝟙₂ g) ⋆ (β ∘₂ α)).
  - apply comp2_h_proper; [symmetry; apply comp2_v_id_l | reflexivity].
  - apply comp2_interchange.
Qed.

(** Compatibility with composition for [whisker_r]. *)

(** [whisker_r] 与复合的相容性。 *)

Theorem whisker_r_comp {K : Bicat} {X Y Z : ObB K}
    {g0 g1 g2 : Cell1 Y Z} (β : g1 ⇒₂ g2) (α : g0 ⇒₂ g1) (f : Cell1 X Y)
  : ((β ∘₂ α) ▷ f) ≈₂ ((β ▷ f) ∘₂ (α ▷ f)).
Proof.
  transitivity ((β ∘₂ α) ⋆ (𝟙₂ f ∘₂ 𝟙₂ f)).
  - apply comp2_h_proper; [reflexivity | symmetry; apply comp2_v_id_l].
  - apply comp2_interchange.
Qed.
