From Cats Require Export
  Cat.Shape.Discrete
  Cat.Shape.Order
  Cat.Shape.Ordinal.
From Cats Require Export Graph.Shape.

(** * Free Cospan and Span Shapes *)
Definition CospanShape
  := FreeCat CospanGraph.
Definition SpanShape
  := CospanShape^op.
Definition ParallelShape
  := FreeCat ParallelGraph.
