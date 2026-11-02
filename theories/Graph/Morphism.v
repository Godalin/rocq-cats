From Cats Require Export Graph.Core.
From Cats.Set Require Export Morphism.

(** * Graph Maps

    Vertex maps are ordinary functions, as for functors on objects. Edge maps
    already carry their respectfulness witnesses. *)

(** * 图映射

    顶点映射是普通函数，与函子的对象映射一致；边映射自带保相等见证。 *)

Record GraphMap (G H : Graph)
  :=
  { vertex_map :> @Vertex G → @Vertex H
  ; edge_map {x y} : EdgeSet x y →r EdgeSet (vertex_map x) (vertex_map y)
  }.

Arguments vertex_map {_ _} _ _.
Arguments edge_map {_ _} _ {_ _}.

Notation "G '→G' H" := (GraphMap G H)
  (at level 99, right associativity) : graph_scope.

(** The graph map acting identically on vertices and edges. *)

(** 在顶点和边上恒等作用的图映射。 *)

Program Definition GraphId (G : Graph)
  : G →G G
  :=
  {|vertex_map x := x
  ; edge_map x y := id_resp
  |}.

(** Compose vertex maps and respectful edge maps. *)

(** 复合顶点映射及保相等边映射。 *)

Program Definition GraphComp {G H K : Graph} (g : H →G K) (f : G →G H)
  : G →G K
  :=
  {|vertex_map x := g (f x)
  ; edge_map x y := edge_map g ∘r edge_map f
  |}.

Infix "∘G" := GraphComp (at level 40, left associativity) : graph_scope.
