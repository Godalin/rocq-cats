From Cats Require Import
  Instance.Set.Simplicial.Vertex.Ordinal
  Instance.Set.Simplicial.Homotopy.Core
  Instance.Set.Simplicial.Vertex.Terminal
  Cat.Core
  Cat.Diagram.Core
  Cat.Functor.Core
  Cat.Natural.

Local Open Scope nat_scope.

(** * Computing through the Ordinal Comparison

    Both directions retain positions and actual ordinal arrows. Face maps
    skip the chosen position, and the two interval endpoints stay distinct. *)

(** * 穿过序数比较进行计算

    双向均保留位置与实际序数箭头；面映射跳过选定位置，两个区间端点仍不同。 *)

Definition ordinal_triangle
  : (Nᵥ(OrdinalObjectsF 2) :
      Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}) 2
  := StandardVertexNerveN 2 2 (simplex_generic 2).

Example generic_vertex_computes (i : Ordinal 2)
  : lower ordinal_triangle i = i.
Proof. reflexivity. Qed.

Example generic_arrow_computes
  : fmap (lower ordinal_triangle) (ordinal_step fin_first) = tt.
Proof. reflexivity. Qed.

Example comparison_round_trip_computes (i : Ordinal 2)
  : lower (OrdinalVertexNerveN 2 2 ordinal_triangle) i = i.
Proof. reflexivity. Qed.

(** The middle face of a triangle is the edge from zero to two. *)

(** 三角形的中间面为从零到二的边。 *)

Definition ordinal_middle_face
  : (Nᵥ(OrdinalObjectsF 2) :
      Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}) 1
  := VertexNerveN (OrdinalVertexMapF (δ[1; fin_next fin_first])) 1
      (StandardVertexNerveN 1 1 (simplex_generic 1)).

Example face_first_vertex_computes
  : lower ordinal_middle_face fin_first = fin_first.
Proof. reflexivity. Qed.

Example face_final_vertex_computes
  : lower ordinal_middle_face (fin_next fin_first) =
      fin_next (fin_next fin_first).
Proof. reflexivity. Qed.

(** Points from the terminal presentation evaluate to the chosen positions. *)

(** 从终呈现出发的点求值为选定位置。 *)

Definition terminal_vertex
  : (Nᵥ(VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set}) :
      Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}) 0
  := ⟨ConstF [Ord 0]
      (C := VertexCat
        VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set}) tt⟩ᵥ.

Example interval_initial_point_computes
  : lower (OrdinalVertexNerveN 1 0
      (VertexNerveN (OrdinalVertexPointF 1 (simplex_interval_position false))
        0 terminal_vertex)) fin_first = fin_first.
Proof. reflexivity. Qed.

Example interval_final_point_computes
  : lower (OrdinalVertexNerveN 1 0
      (VertexNerveN (OrdinalVertexPointF 1 (simplex_interval_position true))
        0 terminal_vertex)) fin_first = fin_next fin_first.
Proof. reflexivity. Qed.
