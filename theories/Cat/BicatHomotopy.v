From Cats Require Import Cat.Core Cat.Functor Cat.Bicategory.

Local Open Scope bicat_scope.

(** * The One-dimensional Shadow of a Bicategory

    Retain the objects and 1-cells, comparing parallel 1-cells by an
    invertible 2-cell. No quotient of representatives is constructed. *)

Program Definition BicatHomotopyCat (K : Bicat) : Cat :=
  {| Ob := ObB K
   ; Hom := @Cell1 K
   ; HomEq X Y := @iso (HomCat X Y)
   ; id X := 𝟙₁ X
   ; comp X Y Z g f := g ∘₁ f
   |}.
Next Obligation.
  intros g g' Hg f f' Hf.
  exists (Hg.1 ⋆ Hf.1).
  apply (functor_is_iso (comp1F X Y Z)
    (X := (g, f)) (Y := (g', f')) (Hg.1, Hf.1)).
  exists (Hg.2.1, Hf.2.1). split; split.
  - exact (fst Hg.2.2).
  - exact (fst Hf.2.2).
  - exact (snd Hg.2.2).
  - exact (snd Hf.2.2).
Defined.
Next Obligation. exact (right_unitor f; right_unitor_iso f). Defined.
Next Obligation. exact (left_unitor f; left_unitor_iso f). Defined.
Next Obligation. exact (associator f g h; associator_iso f g h). Defined.
