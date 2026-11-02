From Cats Require Export Graph.Core.
From Cats.Set Require Export Finite.

(** * Finite Graphs by Their Adjacency Counts

    Finite positions label both vertices and the parallel generators at each
    pair of endpoints. There are no endpoint equality proof fields. *)

(** * 由邻接计数指定的有限图

    有限位置同时标记顶点与每对端点间的平行生成边，不携带端点相等证明字段。 *)

Program Definition FiniteGraph@{o e p +} {n : nat} (k : Fin n → Fin n → nat)
  : Graph@{o e p}
  :=
  {|Vertex := Fin n
  ; EdgeSet x y := FinS (k x y)
  |}.
