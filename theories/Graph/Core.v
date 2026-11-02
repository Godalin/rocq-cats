From Cats.Set Require Export Core.

(** * Directed Graphs with Sets of Edges *)

(** * 边集为广集的有向图 *)

(** Vertices with a specified setoid of directed edges for each endpoint pair. *)

(** 顶点及每对端点之间指定的有向边广集。 *)

Class Graph@{o e p +}
  :=
  { Vertex : Type@{o}
  ; EdgeSet : Vertex → Vertex → SetC@{e p}
  }.

(** The carrier of the specified edge setoid. *)

(** 指定边广集的载体。 *)

Definition Edge {G : Graph} (x y : @Vertex G)
  := carrier (EdgeSet x y).

(** A total index for generators, retaining their dependent endpoints. *)

(** 生成边的总索引保留其依赖端点。 *)

Definition GraphEdges (G : Graph)
  := ∃ x : @Vertex G, ∃ y : @Vertex G, Edge x y.

Declare Scope graph_scope.
Delimit Scope graph_scope with graph.
Open Scope graph_scope.

Notation "x '→[' G ']' y" := (@Edge G x y)
  (at level 50, no associativity) : graph_scope.

(** Discrete graphs have vertices but no generating edges. *)

(** 离散图有顶点而没有生成边。 *)

Program Definition DiscreteGraph (V : Type)
  : Graph
  :=
  {|Vertex := V
  ; EdgeSet x y :=
      {|carrier := Empty_set
      ; carrier_equiv _ _ := unit
      |}
  |}.
Next Obligation.
  split; repeat intro; exact tt.
Defined.
