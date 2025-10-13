From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.

(** * Natural Transformations *)

Class Nat@{o1 h1 o2 h2}
  {C : Cat@{o1 h1}} {D : Cat@{o2 h2}}
  (F G : Functor C D) := mkNat
  { nt (X : @Ob C) : (@Hom D) (F .F0 X) (G .F0 X)

  ; axiom_naturalilty
    : ∀ X Y : @Ob C, ∀ f : Hom X Y,
      nt Y ∘ F .F1 f = G .F1 f ∘ nt X
  }.

Arguments mkNat {_ _ _ _} _ _.
Arguments nt {_ _ _ _} _ _.
Arguments axiom_naturalilty {_ _ _ _} _ {_ _} _.

Check Nat.



Notation "F => G" := (Nat F G)
  (at level 50, no associativity).

Program Instance id_nt {C D : Cat} {F : Functor C D} : F => F
  := { nt _ := id }.
Next Obligation.
  rewrite axiom_id_l.
  rewrite axiom_id_r.
  reflexivity.
Qed.

Program Instance comp_nt {C D : Cat} {F G H : Functor C D}
    (α : G => H) (β : F => G) : F => H
  := { nt X := (nt α X) ∘ (nt β X) }.
Next Obligation.
  rewrite axiom_comp_assoc.
  rewrite (axiom_naturalilty β f).
  rewrite <- (axiom_comp_assoc) at 1.
  rewrite (axiom_naturalilty α f).
  rewrite axiom_comp_assoc.
  reflexivity.
Qed.

Program Instance Fct {C D : Cat} : Cat :=
  { Ob := Functor C D
  ; Hom F G := F => G
  ; id _ := id_nt
  ; comp _ _ _ := comp_nt
  }.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
