From Cats Require Export Cat.Free.

(** * Discrete Index Categories *)

(** * 离散索引范畴 *)

(** The free category on a graph without edges. *)

(** 无边图上的自由范畴。 *)

Definition DiscreteCat (V : Type)
  := FreeCat (DiscreteGraph V).

(** The discrete shape with no objects. *)

(** 没有对象的离散形状。 *)

Definition EmptyShape
  := DiscreteCat Empty_set.
(** The discrete shape with one object. *)

(** 仅有一个对象的离散形状。 *)

Definition PointShape
  := DiscreteCat unit.
(** The discrete shape with two objects. *)

(** 具有两个对象的离散形状。 *)

Definition PairShape
  := DiscreteCat bool.
