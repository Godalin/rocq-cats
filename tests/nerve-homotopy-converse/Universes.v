From Cats Require Import
  Instance.Set.Simplicial.Vertex.HomotopyInv
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Recovering Transformations at Independent Sizes

    Source and target have opposite native carrier/equality profiles. Check
    arbitrary homotopies in both strict orders of the common value sizes,
    including both round trips and respect for homotopy-map equality. *)

(** * 在独立大小下恢复自然变换

    源与目标具有相反的原生载体／相等大小配置。在共同值大小的两种严格次序下
    检查任意同伦，包括两个往返律及对同伦映射相等的保持。 *)

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
      (VertexNerveN F :
        (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
      (VertexNerveN G))
    (E : HomotopyEq H K)
    (L : SimplicialHomotopy
      (VertexNerveN F :
        (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
      (VertexNerveN G)).

(** Value equality below the carrier still recovers an ordinary transformation. *)

(** 值相等低于载体时，仍恢复普通自然变换。 *)

Definition low_value_recovery
  : F ⇒ G
  := VertexNerveInvHomotopyN H.

Definition low_value_homotopy_roundtrip
  : ∃ β : F ⇒ G, HomotopyEq
      (VertexNerveHomotopy (F := F) (G := G) β : SimplicialHomotopy
        (VertexNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
        (VertexNerveN G)) H.
Proof.
  exists (VertexNerveInvHomotopyN H).
  exact (@vertex_nerve_homotopy_β X Y C D T U F G H).
Defined.

Definition low_value_recovery_proper
  : VertexNerveInvHomotopyN H ≈N VertexNerveInvHomotopyN K
  := vertex_nerve_inv_homotopy_proper H K E.

(** The opposite strict order also supports recovery and its full round trip. *)

(** 相反的严格次序也支持恢复及完整往返律。 *)

Definition high_value_recovery
  : F ⇒ G
  := VertexNerveInvHomotopyN L.

Definition high_value_homotopy_roundtrip
  : ∃ β : F ⇒ G, HomotopyEq
      (VertexNerveHomotopy (F := F) (G := G) β : SimplicialHomotopy
        (VertexNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
        (VertexNerveN G)) L.
Proof.
  exists (VertexNerveInvHomotopyN L).
  exact (@vertex_nerve_homotopy_β X Y C D T U F G L).
Defined.

(** Transformation equality is native and independent of the raised values. *)

(** 自然变换相等是原生相等，与提升后的值大小独立。 *)

Definition low_value_transformation_roundtrip
  : VertexNerveInvHomotopyN
      (VertexNerveHomotopy α : SimplicialHomotopy
        (VertexNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
        (VertexNerveN G)) ≈N α
  := vertex_nerve_homotopy_η α.

Definition high_value_transformation_roundtrip
  : VertexNerveInvHomotopyN
      (VertexNerveHomotopy α : SimplicialHomotopy
        (VertexNerveN F :
          (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
        (VertexNerveN G)) ≈N α
  := vertex_nerve_homotopy_η α.

End Levels.
