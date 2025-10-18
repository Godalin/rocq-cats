From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.
From Cats Require Import Cat.Natural.



(** * Adjunctions

    Hom(F - , =) ≅N Hom(- , G =) *)

(* Definition Adjunction {C D : Cat}
    (F : Functor C D) (G : Functor D C)
      {X : @Ob C} {Y : @Ob D}
  := xoF Y ∘F F ≅N G ∘F yoF X. *)
