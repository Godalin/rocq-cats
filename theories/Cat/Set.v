From Cats Require Import Cat.Core.

Program Instance SetC : Cat :=
  { Ob := Type
  ; Hom X Y := X → Y
  ; HomEq _ _ := eq
  }.
Next Obligation.
  repeat split; auto.
  repeat intro. etransitivity.
  apply H. apply H0.
Qed.
