From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Bicategory.Strict.
From Cats Require Import
  Cat.Natural
  Cat.CatCat
  Cat.Bicategory.Homotopy.

(** * A Locally Thin Bicategory from a Category

    Keep the objects and morphisms of [C] as 0-cells and 1-cells. A 2-cell is
    a witness of [HomEq]; parallel 2-cells are always equivalent. Thus proof
    witnesses are retained without requiring them to be equal. *)

(** * 由范畴构造局部薄的双范畴

    [C] 的对象和态射分别作为零胞和一胞，二胞是 [HomEq] 见证，平行二胞总是等价。
    保留证明见证而不要求其原生相等。 *)

Program Definition ThinHomCat (C : Cat) (X Y : @Ob C)
  : Cat
  :=
  {|Ob := Hom X Y
  ; HomSet f g :=
      {|carrier := f ≈ g
      ; carrier_equiv _ _ := unit
      |}
  ; id f := reflexivity f
  ; comp f g h β α := transitivity α β
  |}.
Next Obligation. split; red; intros; exact tt. Defined.
Next Obligation. intros α α' Hα β β' Hβ. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** An invertible 2-cell retains exactly the original arrow equivalence. *)

(** 可逆二胞恰好保留原范畴的箭头相等。 *)

Definition thin_hom_iso_eq {C : Cat} {X Y : @Ob C} (f g : Hom X Y)
  : f ≅[ThinHomCat C X Y] g ↔ f ≈ g.
Proof.
  split.
  - intros H. exact H.1.
  - intros p. exists p, (symmetry p). split; exact tt.
Defined.

(** Horizontal composition of hom-equality witnesses as a hom-category
    functor. *)

(** 将 Hom 相等见证的水平复合组织为 Hom 范畴函子。 *)

Program Definition thin_horizontalF (C : Cat) (X Y Z : @Ob C)
  : Functor (ThinHomCat C Y Z ×C ThinHomCat C X Y) (ThinHomCat C X Z)
  :=
  {|F0 p := fst p ∘ snd p
  ; F1 u v α := @comp_proper C X Y Z
      (fst u) (fst v) (fst α) (snd u) (snd v) (snd α)
  |}.
Next Obligation. intros α β H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** Turn morphism equality into the two-cells of a locally thin bicategory. *)

(** 将态射相等作为局部薄双范畴的二胞。 *)

Program Definition ThinBicat (C : Cat)
  : Bicat
  :=
  {|ObB := @Ob C
  ; HomCat := ThinHomCat C
  ; id1 X := @id X
  ; comp1F := thin_horizontalF C
  ; associator W X Y Z h g f := @comp_assoc C W X Y Z h g f
  ; left_unitor X Y f := @comp_id_l C X Y f
  ; right_unitor X Y f := @comp_id_r C X Y f
  |}.
Next Obligation.
  exists (symmetry (@comp_assoc C W X Y Z h g f)). split; exact tt.
Defined.
Next Obligation. exists (symmetry (@comp_id_l C X Y f)). split; exact tt. Defined.
Next Obligation. exists (symmetry (@comp_id_r C X Y f)). split; exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** The specified strict 1-cell equality is precisely the original [HomEq].
    Its comparison 2-cell is the witness itself. Enable this structure
    locally. *)

(** 指定的严格一胞相等就是原来的 [HomEq]，比较二胞就是该见证；此结构须在使用处
    显式启用。 *)

Program Definition ThinBicat_IsStrictTwoCat (C : Cat)
  : IsStrictTwoCat (ThinBicat C)
      (λ X Y, @Cats.Cat.Core.HomEq C X Y) (λ X Y f g p, p)
  :=
  {|Cell1Eq_Equivalence X Y := @HomEq_Equivalence C X Y
  ; comp1_proper X Y Z := @comp_proper C X Y Z
  ; comp1_id_l X Y f := @comp_id_l C X Y f
  ; comp1_id_r X Y f := @comp_id_r C X Y f
  ; comp1_assoc W X Y Z h g f := @comp_assoc C W X Y Z h g f
  |}.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** Recover an original-category arrow from the thin homotopy category. *)

(** 从薄同伦范畴恢复原范畴箭头。 *)

Program Definition FromThinHomotopyF (C : Cat)
  : Functor (BicatHomotopyCat (ThinBicat C)) C
  :=
  {|F0 X := X
  ; F1 X Y f := f
  ; functor_fmap_proper X Y f g H := fst (thin_hom_iso_eq (C := C) f g) H
  |}.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** View an original-category arrow in its thin homotopy category. *)

(** 将原范畴箭头视为薄同伦范畴的箭头。 *)

Program Definition ToThinHomotopyF (C : Cat)
  : Functor C (BicatHomotopyCat (ThinBicat C))
  :=
  {|F0 X := X
  ; F1 X Y f := f
  ; functor_fmap_proper X Y f g H := snd (thin_hom_iso_eq (C := C) f g) H
  |}.
Next Obligation. apply (snd (thin_hom_iso_eq (C := C) _ _)). reflexivity. Defined.
Next Obligation. apply (snd (thin_hom_iso_eq (C := C) _ _)). reflexivity. Defined.

(** The thin bicategory's homotopy category is equivalent to the original
    category. *)

(** 薄双范畴的同伦范畴等价于原范畴。 *)

Definition thin_bicat_homotopy_equiv (C : Cat)
  : BicatHomotopyCat (ThinBicat C) ≃C C.
Proof.
  exists (FromThinHomotopyF C), (ToThinHomotopyF C). split.
  - unshelve notypeclasses refine (({|nt := _
                                    |}); _).
    + exact (λ X, @id X).
    + intros X Y f. apply (snd (thin_hom_iso_eq (C := C) _ _)). cbn. carw.
    + intros X. exists (@id X). split;
        apply (snd (thin_hom_iso_eq (C := C) _ _));
        exact (@comp_id_l C X X (@Cats.Cat.Core.id C X)).
  - unshelve notypeclasses refine (({|nt := _
                                    |}); _).
    + exact (λ X, @id X).
    + intros X Y f. cbn. carw.
    + intros X. exists (@id X). split; apply comp_id_l.
Defined.
