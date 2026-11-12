From Cats Require Import
  Instance.Set.Simplicial.Vertex.Homotopy
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Independent Sizes in the Nerve Homotopy Bridge

    Source and target use opposite native carrier/equality profiles.
    The common simplicial values are checked in both strict size orders. *)

(** * nerve 同伦桥梁的独立大小

    源与目标使用相反的原生载体／相等配置，共同单纯值检查两种严格大小次序。 *)

Section Levels.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.

Context (X : SetC@{o e}) (Y : SetC@{h o})
    (C : Cat@{o h e l l}) (D : Cat@{h e o l l})
    (T : Functor (EqGpd X) C) (U : Functor (EqGpd Y) D)
    (F G : T →ᵥ U) (α β : F ⇒ G) (H : α ≈N β).

(** The generic construction keeps native hom sizes independent. *)

(** 通用构造保持原生 Hom 大小独立。 *)

Definition native_prism
  : Functor (VertexCat T ×C [Ord 1]) (VertexCat U)
  := NaturalPrismF α.

(** Value equality can lie strictly below the value carrier. *)

(** 值相等可严格低于值载体。 *)

Definition low_value_nerve_homotopy
  : SimplicialHomotopy
      (VertexNerveN F :
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
      (VertexNerveN G)
  := VertexNerveHomotopy α.

Definition low_value_nerve_homotopy_eq
  : HomotopyEq low_value_nerve_homotopy (VertexNerveHomotopy β)
  := vertex_nerve_homotopy_proper α β H.

Definition low_value_nerve_endpoint
  : (homotopy_map low_value_nerve_homotopy ∘Nv
      SimplicialEndpointN Nᵥ(T) false) ≈N VertexNerveN F
  := vertex_nerve_homotopy_0 α.

(** Value equality can instead lie strictly above the value carrier. *)

(** 值相等也可严格高于值载体。 *)

Definition high_value_nerve_homotopy
  : SimplicialHomotopy
      (VertexNerveN F :
        (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ Nᵥ(U))
      (VertexNerveN G)
  := VertexNerveHomotopy α.

Definition high_value_nerve_endpoint
  : (homotopy_map high_value_nerve_homotopy ∘Nv
      SimplicialEndpointN Nᵥ(T) true) ≈N VertexNerveN G
  := vertex_nerve_homotopy_1 α.

(** Identity comparison uses the equality of stored maps, not proof fields. *)

(** 恒等比较使用所存映射的相等，不比较证明字段。 *)

Definition low_value_nerve_identity
  : HomotopyEq
      (VertexNerveHomotopy (F := F) (idN : F ⇒ F) :
        SimplicialHomotopy
          (VertexNerveN F :
            (Nᵥ(T) : Functor (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ Nᵥ(U))
          (VertexNerveN F))
      (SimplicialConstantHomotopy (VertexNerveN F))
  := vertex_nerve_homotopy_id F.

End Levels.
