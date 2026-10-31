From Cats Require Import Cat.Core Cat.Functor Cat.TwoCategory.

(** * A Locally Thin Bicategory from a Category

    Keep the objects and morphisms of [C] as 0-cells and 1-cells. A 2-cell
    is a witness of [HomEq]; parallel 2-cells are always equivalent.
    Thus proof witnesses are retained without requiring them to be equal. *)

Program Definition ThinHomCat (C : Cat) (X Y : @Ob C) : Cat :=
  {| Ob := Hom X Y
   ; Hom f g := f ≈ g
   ; HomEq _ _ _ _ := unit
   ; id f := reflexivity f
   ; comp f g h β α := transitivity α β
   |}.
Next Obligation. split; red; intros; exact tt. Defined.
Next Obligation. intros α α' Hα β β' Hβ. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

Program Definition thin_horizontalF (C : Cat) (X Y Z : @Ob C)
  : Functor (ThinHomCat C Y Z ×C ThinHomCat C X Y) (ThinHomCat C X Z) :=
  {| F0 p := fst p ∘ snd p
   ; F1 u v α := @comp_proper C X Y Z
       (fst u) (fst v) (fst α) (snd u) (snd v) (snd α)
   |}.
Next Obligation. intros α β H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

Program Definition ThinBicat (C : Cat) : Bicat :=
  {| ObB := @Ob C
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
    Its comparison 2-cell is the witness itself. Enable this structure locally. *)
Program Definition ThinBicat_IsStrictTwoCat (C : Cat)
  : IsStrictTwoCat (ThinBicat C)
      (λ X Y, @Cats.Cat.Core.HomEq C X Y) (λ X Y f g p, p) :=
  {| Cell1Eq_Equivalence X Y := @HomEq_Equivalence C X Y
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
