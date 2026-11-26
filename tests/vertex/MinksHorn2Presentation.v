From Cats Require Import
  Instance.Set.Simplicial.Vertex.Filling
  Instance.Set.Simplicial.Vertex.Kan
  Instance.Set.Simplicial.Vertex.Monoid
  Instance.Bool.Action
  Instance.Bool.Commutative.

(** Packaging never chooses a presentation for an arbitrary whole horn. *)

Section SelectedPresentation.
Universes u p.
Context {X : SetC} {C : Cat} (T : Fct (EqGpd X) C)
    {i : Ordinal 2}
    (h : HornS (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2 i).

Fail Definition unchosen_presentation
  : HasHorn2Presentation T h
  := ltac:(typeclasses eauto).

Context (H K : HasHorn2Presentation T h).

Definition selected_presentation
  : Horn2Presentation T h
  := MakeHorn2Presentation T h H.

Local Existing Instance K.

Example selected_component_kept
  : hasHorn2Presentation T h selected_presentation = H
  := eq_refl.

Example selected_vertex0_kept
  : horn2_vertex0 T selected_presentation = horn2_vertex0 T H
  := eq_refl.

Example selected_vertex1_kept
  : horn2_vertex1 T selected_presentation = horn2_vertex1 T H
  := eq_refl.

Example selected_vertex2_kept
  : horn2_vertex2 T selected_presentation = horn2_vertex2 T H
  := eq_refl.

Example selected_local_horn_kept
  : horn2_local T selected_presentation = horn2_local T H
  := eq_refl.

Example selected_realization_kept
    (q : TriangleS (VtxCat T)
      (horn2_vertex0 T H) (horn2_vertex1 T H) (horn2_vertex2 T H))
    (e : is_horn2_filler (horn2_local T H) q)
  : horn2_presentation T selected_presentation q e =
      horn2_presentation T H q e
  := eq_refl.

(** The actual reconstruction consumer returns a package; it is not a
    registered choice of a local presentation for future searches. *)

Definition reconstructed_component
  : HasHorn2Presentation T h
  := hasHorn2Presentation T h (horn2_reconstruct T h).

End SelectedPresentation.

Fail Check Cats.Instance.Set.Simplicial.Vertex.Filling.Build_Horn2Presentation.

(** All three orientations retain nontrivial arrow computation through
    reconstruction, local selected filling, and realization. *)

Module ActualBooleanHorns.
Local Open Scope nat_scope.

Definition T := MonoidObjF BoolS_Monoid.
Definition triangle
  : (Nᵥ(T) : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) 2
  := △₂[T; tt; tt; tt] (true, false).

Definition h0 := triangle↾Λ[Nᵥ(T); 2; fin_first].
Definition h1 := triangle↾Λ[Nᵥ(T); 2; fin_next fin_first].
Definition h2 := triangle↾Λ[Nᵥ(T); 2; fin_next (fin_next fin_first)].

Example reconstruction_0_computes
  : horn2_local T (horn2_reconstruct T h0) = (true, true)
  := eq_refl.

Example reconstruction_1_computes
  : horn2_local T (horn2_reconstruct T h1) = (true, false)
  := eq_refl.

Example reconstruction_2_computes
  : horn2_local T (horn2_reconstruct T h2) = (false, true)
  := eq_refl.

Definition fillers (i : Ordinal 2)
  := vertex_gpd_horn2_HasFillers T
    (HC := VtxCat_IsGpd T (HC := BoolGpd_IsGpd)) i.

Example outer_0_filler_computes
  : fmap (lower (@horn_fill _ _ _ (fillers fin_first) h0).1)
      (ordinal_step (fin_next fin_first)) = false
  := eq_refl.

Example inner_filler_computes
  : fmap (lower (@horn_fill _ _ _ (fillers (fin_next fin_first)) h1).1)
      (ordinal_step fin_first) = true
  := eq_refl.

Example outer_2_filler_computes
  : fmap (lower (@horn_fill _ _ _
      (fillers (fin_next (fin_next fin_first))) h2).1)
      (ordinal_step fin_first) = true
  := eq_refl.

End ActualBooleanHorns.

(** The original native sizes and both ambient nerve equality orders
    remain independent in the complete package and selected component. *)

Section StrictSizes.
Universes e h o l u p.
Constraint e < h, h < o, o < l, l < u, u < p.
Context (X : SetC@{o e}) (Y : SetC@{e o})
    (C : Cat@{o h e l l}) (D : Cat@{e h o l l})
    (T : Fct (EqGpd X) C) (S : Fct (EqGpd Y) D)
    (i : Ordinal 2)
    (a : HornS (Nᵥ(T) : Fct (Δ^op) SetCat@{u h _ _ _ _ _}) 2 i)
    (b : HornS (Nᵥ(S) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 2 i)
    (H : HasHorn2Presentation T a) (K : HasHorn2Presentation S b).

Definition lower_equality_presentation
  : Horn2Presentation T a
  := MakeHorn2Presentation T a H.

Definition higher_equality_presentation
  : Horn2Presentation S b
  := MakeHorn2Presentation S b K.

Example lower_equality_component_kept
  : hasHorn2Presentation T a lower_equality_presentation = H
  := eq_refl.

Example higher_equality_component_kept
  : hasHorn2Presentation S b higher_equality_presentation = K
  := eq_refl.

Definition lower_equality_reconstruction
  : Horn2Presentation T a
  := horn2_reconstruct T a.

Definition higher_equality_reconstruction
  : Horn2Presentation S b
  := horn2_reconstruct S b.

End StrictSizes.

Fail Definition different_missing_face
  : Horn2Presentation ActualBooleanHorns.T ActualBooleanHorns.h1
  := horn2_reconstruct ActualBooleanHorns.T ActualBooleanHorns.h0.
