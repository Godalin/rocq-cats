From Cats Require Import
  Instance.Set.Simplicial.Vertex.HomotopyInv
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Recovering Transformations at Independent Sizes

    Source and target have opposite native carrier/equality profiles. Check
    arbitrary homotopies in both strict orders of the common value sizes,
    including both round trips and respect for homotopy-map equality. *)

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
    (F G : T →ᵥ U) (α : F ⇒ G)
    (H K : SimplicialHomotopy
      (VtxNerveN F :
        (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
      (VtxNerveN G))
    (E : HomotopyEq H K)
    (L : SimplicialHomotopy
      (VtxNerveN F :
        (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
      (VtxNerveN G)).

(** Value equality below the carrier still recovers an ordinary transformation. *)

Definition low_value_recovery
  : F ⇒ G
  := VtxNerveInvHomotopyN H.

Definition low_value_homotopy_roundtrip
  : ∃ β : F ⇒ G, HomotopyEq
      (VtxNerveHomotopy (F := F) (G := G) β : SimplicialHomotopy
        (VtxNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
        (VtxNerveN G)) H.
Proof.
  exists (VtxNerveInvHomotopyN H).
  exact (@vertex_nerve_homotopy_β X Y C D T U F G H).
Defined.

Definition low_value_recovery_proper
  : VtxNerveInvHomotopyN H ≈N VtxNerveInvHomotopyN K
  := vertex_nerve_inv_homotopy_proper H K E.

(** The opposite strict order also supports recovery and its full round trip. *)

Definition high_value_recovery
  : F ⇒ G
  := VtxNerveInvHomotopyN L.

Definition high_value_homotopy_roundtrip
  : ∃ β : F ⇒ G, HomotopyEq
      (VtxNerveHomotopy (F := F) (G := G) β : SimplicialHomotopy
        (VtxNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
        (VtxNerveN G)) L.
Proof.
  exists (VtxNerveInvHomotopyN L).
  exact (@vertex_nerve_homotopy_β X Y C D T U F G L).
Defined.

(** Transformation equality is native and independent of the raised values. *)

Definition low_value_transformation_roundtrip
  : VtxNerveInvHomotopyN
      (VtxNerveHomotopy α : SimplicialHomotopy
        (VtxNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
        (VtxNerveN G)) ≈N α
  := vertex_nerve_homotopy_η α.

Definition high_value_transformation_roundtrip
  : VtxNerveInvHomotopyN
      (VtxNerveHomotopy α : SimplicialHomotopy
        (VtxNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
        (VtxNerveN G)) ≈N α
  := vertex_nerve_homotopy_η α.

End Levels.
