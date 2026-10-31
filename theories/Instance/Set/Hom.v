From Cats Require Import Cat.Core Cat.Functor Instance.Set.Core.

(** * Hom-Functors *)

Definition ℎ1 {C : Cat} (X : Ob) := λ Y, Hom X Y.
Definition ℎ2 {C : Cat} (X : Ob) := λ Y, Hom Y X.

Program Definition ℎ1F {C : Cat} (X : Ob) : Functor C SetCat :=
  {|F0 := ℎ1 X
  ; F1 Y Y' (f : Hom Y Y') := f _*
  |}.
Next Obligation. intros f f' Hf g. simpl. rewrite Hf. cato. Qed.
Next Obligation. intros f. simpl. cato. Qed.
Next Obligation. intros x. simpl. apply comp_assoc. Qed.

Notation "'Hom(' X  ',-)'" := (ℎ1F X).

Program Definition ℎ2F {C : Cat} (X : Ob)
  : Functor (op C) SetCat :=
  {|F0 := ℎ2 X
  ; F1 Y Y' (f : (@Hom C) Y' Y) := f ^*
  |}.
Next Obligation. intros f f' Hf g. simpl. rewrite Hf. cato. Qed.
Next Obligation. intros f. simpl. cato. Qed.
Next Obligation. intros x. simpl. cacl. Qed.

Notation "'Hom(-,'  X ')'" := (ℎ2F X).

Program Canonical bi_comp {C : Cat} {X' X Y Y' : @Ob C}
    (f : (@Hom op C) X X') (g : Hom Y Y')
  : (Hom X Y) →r (Hom X' Y')
  := {|func := λ h, g ∘ h ∘ f |}.
Next Obligation. intros h h' Hh. rewrite Hh. cato. Qed.

Program Definition HomF {C : Cat}
  : Functor (op C ×C C) SetCat :=
  {|F0 X := (@Hom C) (fst X) (snd X)
  ; F1 _ _ f := bi_comp (fst f) (snd f)
  |}.
Next Obligation. simpl. intros [f g] [f' g'] [Hf Hg].
  simpl. intros h. simpl.
  rewrite Hf, Hg. reflexivity.
Qed.
Next Obligation. simpl. intros h. simpl; carw. Qed.
Next Obligation. simpl. intros g. simpl. repeat cacr. Qed.
