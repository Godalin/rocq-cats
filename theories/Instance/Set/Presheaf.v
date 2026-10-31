From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.
From Cats Require Import Cat.Natural.
From Cats Require Import Instance.Set.Core Instance.Set.Hom.



(** * The Category of Presheaves *)

Definition Psh C := Fct (op C) SetCat.

Section Psh.
Context `{C : Cat}.

Program Canonical Embedding : Functor C (Psh C) :=
  {|F0 := ℎ2F
  ; F1 X Y f := f _*N
  |}.
Next Obligation. apply nt_comp_post_id. Qed.
Next Obligation. apply nt_comp_post_comp. Qed.

End Psh.
