From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.
From Cats Require Import Cat.Natural.
From Cats Require Import Cat.Set.



(** * The Category of Presheaves *)

Definition Psh C := Fct (op C) SetCat.

Section Psh.
Context `{C : Cat}.

Program Definition nt_comp_post {X Y : @Ob C} (f : Hom X Y)
  : Hom(-, X ) => Hom(-, Y ) :=
  {|nt X := f _* |}.
Next Obligation. intros h. simpl. cacl. Qed.

Notation "f _*N" := (nt_comp_post f).

Program Canonical Embedding : Functor C (Psh C) :=
  {|F0 := ℎ2F
  ; F1 X Y f := f _*N
  |}.
Next Obligation. intros h h' Hh O. simpl. intros i.
  simpl. rewrite Hh. reflexivity.
Qed.
Next Obligation. intros O; simpl. intros f. simpl. cato. Qed.
Next Obligation. intros O; simpl. intros h. simpl. cacl. Qed.

End Psh.
