From Cats.Set Require Export Core.

(** * Directed Graphs with Sets of Edges *)
Class Graph@{o e p +} :=
  { Vertex : Type@{o}
  ; EdgeSet : Vertex → Vertex → SetC@{e p}
  }.

Definition Edge {G : Graph} (x y : @Vertex G) := carrier (EdgeSet x y).

(** A total index for generators, retaining their dependent endpoints. *)
Definition GraphEdges (G : Graph) := ∃ x : @Vertex G, ∃ y : @Vertex G, Edge x y.

Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Open Scope graph_scope.

Notation "x '→[' G ']' y" := (@Edge G x y)
  (at level 50, no associativity) : graph_scope.

(** Discrete graphs have vertices but no generating edges. *)
Program Definition DiscreteGraph (V : Type) : Graph :=
  {| Vertex := V
   ; EdgeSet x y := {| carrier := Empty_set; carrier_equiv _ _ := unit |} |}.
Next Obligation.
  split; repeat intro; exact tt.
Defined.
