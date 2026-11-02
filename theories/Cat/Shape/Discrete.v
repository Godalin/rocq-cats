From Cats Require Export Cat.Free.

(** * Discrete Index Categories *)
Definition DiscreteCat (V : Type)
  := FreeCat (DiscreteGraph V).

Definition EmptyShape
  := DiscreteCat Empty_set.
Definition PointShape
  := DiscreteCat unit.
Definition PairShape
  := DiscreteCat bool.
