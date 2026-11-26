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

Definition ordinal_triangle
  : (Nᵥ(OrdinalObjF 2) :
      Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) 2
  := StandardVtxNerveN 2 2 (simplex_generic 2).

Example generic_vertex_computes (i : Ordinal 2)
  : lower ordinal_triangle i = i.
Proof. reflexivity. Qed.

Example generic_arrow_computes
  : fmap (lower ordinal_triangle) (ordinal_step fin_first) = tt.
Proof. reflexivity. Qed.

Example comparison_round_trip_computes (i : Ordinal 2)
  : lower (OrdinalVtxNerveN 2 2 ordinal_triangle) i = i.
Proof. reflexivity. Qed.

(** The middle face of a triangle is the edge from zero to two. *)

Definition ordinal_middle_face
  : (Nᵥ(OrdinalObjF 2) :
      Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) 1
  := VtxNerveN (OrdinalVtxMapF (δ[1; fin_next fin_first])) 1
      (StandardVtxNerveN 1 1 (simplex_generic 1)).

Example face_first_vertex_computes
  : lower ordinal_middle_face fin_first = fin_first.
Proof. reflexivity. Qed.

Example face_final_vertex_computes
  : lower ordinal_middle_face (fin_next fin_first) =
      fin_next (fin_next fin_first).
Proof. reflexivity. Qed.

(** Points from the terminal presentation evaluate to the chosen positions. *)

Definition terminal_vertex
  : (Nᵥ(VtxTerminalObjF@{Set Set Set Set Set Set Set Set}) :
      Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) 0
  := ⟨ConstF [Ord 0]
      (C := VtxCat
        VtxTerminalObjF@{Set Set Set Set Set Set Set Set}) tt⟩ᵥ.

Example interval_initial_point_computes
  : lower (OrdinalVtxNerveN 1 0
      (VtxNerveN (OrdinalVtxPointF 1 (simplex_interval_position false))
        0 terminal_vertex)) fin_first = fin_first.
Proof. reflexivity. Qed.

Example interval_final_point_computes
  : lower (OrdinalVtxNerveN 1 0
      (VtxNerveN (OrdinalVtxPointF 1 (simplex_interval_position true))
        0 terminal_vertex)) fin_first = fin_next fin_first.
Proof. reflexivity. Qed.
