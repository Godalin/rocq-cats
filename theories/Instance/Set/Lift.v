From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Instance.Set.Core.

(** * Raising the Ambient Set Universes

    Carrier and equality witnesses are raised independently. This is an
    explicit wrapper, not a resizing principle. *)

(** * 提升环境集合宇宙

    载体与相等见证独立提升，这是显式包装，不是大小重设原理。 *)

Program Definition LiftF@{u p +}
  : Fct SetCat SetCat@{u p _ _ _ _ _}
  :=
  {|fobj X := LiftS@{_ _ u p} X
  ; fmap X Y f := f^↑S
  ; isFct :=
      {|fmap_proper X Y f g H x := Lift (H (lower x))
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros [x]. exact (Lift (reflexivity x)). Qed.
Next Obligation. intros [x]. exact (Lift (reflexivity (f (g x)))). Qed.
