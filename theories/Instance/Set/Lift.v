From Cats Require Import Cat.Core Cat.Functor Instance.Set.Core.

(** * Raising the Ambient Set Universes

    Carrier and equality witnesses are raised independently. This is an
    explicit wrapper, not a resizing principle. *)

Program Definition LiftF@{u p +}
  : Functor SetCat SetCat@{u p _ _ _ _ _} :=
  {| F0 X := LiftS@{_ _ u p} X
   ; F1 X Y f := f^↑S
   ; functor_fmap_proper X Y f g H x := {| lower := H (lower x) |} |}.
Next Obligation. intros [x]. exact {| lower := reflexivity x |}. Defined.
Next Obligation. intros [x]. exact {| lower := reflexivity (f (g x)) |}. Defined.
