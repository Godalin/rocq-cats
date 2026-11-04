From Cats Require Export
  Cat.Diagram.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal.

(** * Cones from an Initial Diagram Position *)

(** * 从图式的始位置出发的锥 *)

(** The unique arrows from an initial position give a cone whose apex is
    the value of the diagram there. Only a candidate universal property is
    needed, without a chosen initial-object structure. *)

(** 从始位置出发的唯一箭头给出以图式在该处的值为顶点的锥。只需候选泛性质，
    不要求选定的始对象结构。 *)

Program Definition InitialCone {J C : Cat} {j : @Ob J}
    (Hj : is_initial j) (F : Functor J C)
  : F j ⇒Δ F
  :=
  {|nt k := fmap F (Hj k).1
  |}.
Next Obligation.
  rewrite comp_id_r, <- functor_comp.
  apply functor_fmap_proper. symmetry.
  exact (@that _ _ _ _ _ (Hj Y).2 _ I).
Defined.
