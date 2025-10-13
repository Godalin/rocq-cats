From Cats Require Import Cat.Core.

Program Instance SetC : Cat :=
  { Ob := Type
  ; Hom X Y := X → Y
  }.
