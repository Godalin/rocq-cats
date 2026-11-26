From Cats Require Import
  Instance.Set.Simplicial.Vertex.Homotopy
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Independent Sizes in the Nerve Homotopy Bridge

    Fix label setoids [X], [Y], categories [C], [D] and object actions
    [T], [U] under the displayed chain of levels. For functors [F], [G]
    and pointwise equal transformations [α], [β], check the prism,
    homotopy, endpoint and identity interfaces at the common value sizes.
    Source and target use opposite native carrier/equality profiles.
    The common simplicial values are checked in both strict size orders. *)

Section Levels.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.

Context (X : SetC@{o e}) (Y : SetC@{h o})
    (C : Cat@{o h e l l}) (D : Cat@{h e o l l})
    (T : Fct (EqGpd X) C) (U : Fct (EqGpd Y) D)
    (F G : T →ᵥ U) (α β : F ⇒ G) (H : α ≈N β).

(** The generic construction keeps native hom sizes independent. *)

Definition native_prism
  : Fct (VtxCat T ×C [Ord 1]) (VtxCat U)
  := NatPrismF α.

(** Value equality can lie strictly below the value carrier. *)

Definition low_value_nerve_homotopy
  : SimplicialHomotopy
      (VtxNerveN F :
        (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
      (VtxNerveN G)
  := VtxNerveHomotopy α.

Definition low_value_nerve_homotopy_eq
  : HomotopyEq low_value_nerve_homotopy (VtxNerveHomotopy β)
  := vertex_nerve_homotopy_proper α β H.

Definition low_value_nerve_endpoint
  : (homotopy_map low_value_nerve_homotopy ∘Nv
      SimplicialEndpointN Nᵥ(T) false) ≈N VtxNerveN F
  := vertex_nerve_homotopy_0 α.

(** Value equality can instead lie strictly above the value carrier. *)

Definition high_value_nerve_homotopy
  : SimplicialHomotopy
      (VtxNerveN F :
        (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
      (VtxNerveN G)
  := VtxNerveHomotopy α.

Definition high_value_nerve_endpoint
  : (homotopy_map high_value_nerve_homotopy ∘Nv
      SimplicialEndpointN Nᵥ(T) true) ≈N VtxNerveN G
  := vertex_nerve_homotopy_1 α.

(** Identity comparison uses the equality of stored maps, not proof fields. *)

Definition low_value_nerve_identity
  : HomotopyEq
      (VtxNerveHomotopy (F := F) (IdN : F ⇒ F) :
        SimplicialHomotopy
          (VtxNerveN F :
            (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
          (VtxNerveN F))
      (SimplicialConstantHomotopy (VtxNerveN F))
  := vertex_nerve_homotopy_id F.

End Levels.
