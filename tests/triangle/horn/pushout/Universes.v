From Cats Require Import
  Instance.Set.Simplicial.TriangleAttachment.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Concrete Attachments at Strict Value Bounds *)

(** ** Lower Equality

    Fix a missing parameter face and an arbitrary step. Geometry needs
    no target choice; extension consumes only this step's selected horn.
    Carrier and specified-equality levels are strictly different. *)

Section lowerSizes.
Universes l u p.
Constraint l < u, u < p.
Context (r : Ordinal 2) (s : Ordinal 8).
Let A
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := TriangleHornStage r (fin_rank s).
Let P
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := TriangleHornStage r (S (fin_rank s)).
Let D
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := Δ[S (simplex_triangle_horn_face_dim s)].
Let L
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := Λ[S (simplex_triangle_horn_face_dim s); simplex_triangle_horn_missing r s].

Definition lower_stage
  : Fct (Δ^op) SetCat@{u l _ _ _ _ _}
  := P.

Definition lower_cell_iso
  : (D : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ≅N
      RegionPsh (TriangleHornCellRegion r s)
  := (TriangleHornCellImageN r s; triangle_horn_cell_image_iso r s).

Definition lower_union_iso
  : P ≅N (TriangleHornStepUnion r s : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
  := (TriangleHornNextUnionN r s; triangle_horn_next_union_iso r s).

Definition lower_overlap
  : RegionPsh (RegionIntersection (TriangleHornRegion r (fin_rank s))
      (TriangleHornCellRegion r s)) ⇒ L
  := TriangleHornOverlapN r s.

Definition lower_comm
  : (TriangleHornStageInclusionN r s ∘Nv TriangleHornAttachingN r s) ≈N
      (TriangleHornStageCellN r s ∘Nv (ιΛ[S (simplex_triangle_horn_face_dim s);
        simplex_triangle_horn_missing r s] : L ⇒ D))
  := triangle_horn_attachment_comm r s.

Definition lower_pushout
  : is_pushout (C := FctCat (Δ^op) SetCat@{u l _ _ _ _ _})
      (TriangleHornAttachingN r s) (ιΛ[S (simplex_triangle_horn_face_dim s);
        simplex_triangle_horn_missing r s] : L ⇒ D)
      P (TriangleHornStageInclusionN r s) (TriangleHornStageCellN r s)
  := triangle_horn_attachment_pushout r s.

Definition lower_final_iso
  : (TriangleHornStage r 9 : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) ≅N
      TriangleHornAmbient
  := (RegionInclusionN (TriangleHornRegion r 9); triangle_horn_final_iso r).

Context {X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}}.

Definition lower_determine (k l : P ⇒ X)
    (E : (k ∘Nv TriangleHornStageInclusionN r s) ≈N
      (l ∘Nv TriangleHornStageInclusionN r s))
    (F : (k ∘Nv TriangleHornStageCellN r s) ≈N
      (l ∘Nv TriangleHornStageCellN r s))
  : k ≈N l
  := triangle_horn_attachment_ext r s k l E F.

Context (K : HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s)) (a : A ⇒ X).

Definition lower_extension
  := TriangleHornStepExtension r s K a.

End lowerSizes.

(** ** Higher Equality

    Fix a missing parameter face and an arbitrary step. Geometry needs
    no target choice; extension consumes only this step's selected horn.
    Carrier and specified-equality levels are strictly different. *)

Section higherSizes.
Universes l u p.
Constraint l < u, u < p.
Context (r : Ordinal 2) (s : Ordinal 8).
Let A
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := TriangleHornStage r (fin_rank s).
Let P
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := TriangleHornStage r (S (fin_rank s)).
Let D
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Δ[S (simplex_triangle_horn_face_dim s)].
Let L
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := Λ[S (simplex_triangle_horn_face_dim s); simplex_triangle_horn_missing r s].

Definition higher_stage
  : Fct (Δ^op) SetCat@{u p _ _ _ _ _}
  := P.

Definition higher_cell_iso
  : (D : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      RegionPsh (TriangleHornCellRegion r s)
  := (TriangleHornCellImageN r s; triangle_horn_cell_image_iso r s).

Definition higher_union_iso
  : P ≅N (TriangleHornStepUnion r s : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  := (TriangleHornNextUnionN r s; triangle_horn_next_union_iso r s).

Definition higher_overlap
  : RegionPsh (RegionIntersection (TriangleHornRegion r (fin_rank s))
      (TriangleHornCellRegion r s)) ⇒ L
  := TriangleHornOverlapN r s.

Definition higher_comm
  : (TriangleHornStageInclusionN r s ∘Nv TriangleHornAttachingN r s) ≈N
      (TriangleHornStageCellN r s ∘Nv (ιΛ[S (simplex_triangle_horn_face_dim s);
        simplex_triangle_horn_missing r s] : L ⇒ D))
  := triangle_horn_attachment_comm r s.

Definition higher_pushout
  : is_pushout (C := FctCat (Δ^op) SetCat@{u p _ _ _ _ _})
      (TriangleHornAttachingN r s) (ιΛ[S (simplex_triangle_horn_face_dim s);
        simplex_triangle_horn_missing r s] : L ⇒ D)
      P (TriangleHornStageInclusionN r s) (TriangleHornStageCellN r s)
  := triangle_horn_attachment_pushout r s.

Definition higher_final_iso
  : (TriangleHornStage r 9 : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      TriangleHornAmbient
  := (RegionInclusionN (TriangleHornRegion r 9); triangle_horn_final_iso r).

Context {X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}}.

Definition higher_determine (k l : P ⇒ X)
    (E : (k ∘Nv TriangleHornStageInclusionN r s) ≈N
      (l ∘Nv TriangleHornStageInclusionN r s))
    (F : (k ∘Nv TriangleHornStageCellN r s) ≈N
      (l ∘Nv TriangleHornStageCellN r s))
  : k ≈N l
  := triangle_horn_attachment_ext r s k l E F.

Context (K : HasHornFillers X (S (simplex_triangle_horn_face_dim s))
      (simplex_triangle_horn_missing r s)) (a : A ⇒ X).

Definition higher_extension
  := TriangleHornStepExtension r s K a.

End higherSizes.
