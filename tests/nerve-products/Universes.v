From Cats Require Import
  Instance.Set.Simplicial.Vertex.Product
  Instance.Set.Simplicial.Vertex.Terminal
  Cat.Core
  Cat.Functor.Product
  Cat.Natural
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Product.

(** * Independent Sizes for Vertex Nerve Products

    Exchange the native object and hom equality profiles of the factors.
    Common value equality is tested strictly below and above its carrier,
    without assuming that either selected category is a groupoid. *)

(** * 顶点 nerve 积的独立大小

    交换两个因子的原生对象及 Hom 相等大小；共同值相等分别严格低于及高于其
    载体，不假定任一选定范畴是群胚。 *)

Section Products.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.
Context (X : SetC@{o e}) (Y : SetC@{e o})
    (C : Cat@{o h e l l}) (D : Cat@{e h o l l})
    (T : Functor (EqGpd X) C) (U : Functor (EqGpd Y) D).

(** Product comparison with value equality below the value carrier. *)

(** 值相等低于值载体的积比较。 *)

Definition low_eq_product_iso
  : (Nᵥ(VertexProductObjectsF T U) :
      Functor (Δ^op) SetCat@{u o _ _ _ _ _}) ≅N VertexNerveProduct T U
  := vertex_nerve_product_iso T U.

(** Product comparison with value equality above the value carrier. *)

(** 值相等高于值载体的积比较。 *)

Definition high_eq_product_iso
  : (Nᵥ(VertexProductObjectsF T U) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N VertexNerveProduct T U
  := vertex_nerve_product_iso T U.

(** Exchange the two native size profiles. *)

(** 交换两个原生大小配置。 *)

Definition reverse_product_iso
  : (Nᵥ(VertexProductObjectsF U T) :
      Functor (Δ^op) SetCat@{u o _ _ _ _ _}) ≅N VertexNerveProduct U T
  := vertex_nerve_product_iso U T.

(** The native correspondence also admits a larger arbitrary probe. *)

(** 原生对应也允许更大且任意的探测范畴。 *)

Definition native_diagram_product_iso (J : Cat@{e h o l l})
  : VertexDiagramS (VertexProductObjectsF T U) J ≅[SetCat]
      (VertexDiagramS T J ×S VertexDiagramS U J)
  := vertex_diagram_product_iso T U J.

(** Terminal diagram comparison must not force the probe to be small. *)

(** 终图式比较不能迫使探测范畴变为小范畴。 *)

Definition native_diagram_terminal_iso (J : Cat@{e h o l l})
  : VertexDiagramS VertexTerminalObjectsF J ≅[SetCat] UnitS@{l o}
  := vertex_diagram_terminal_iso J.

(** Naturality exchanges factors with different native size profiles. *)

(** 自然性允许交换原生大小配置不同的因子。 *)

Definition exchanged_product_naturality (F : T →ᵥ U) (G : U →ᵥ T)
  : (VertexNerveProductN U T ∘Nv VertexNerveN (VertexProductF F G) :
      (Nᵥ(VertexProductObjectsF T U) :
        Functor (Δ^op) SetCat@{u o _ _ _ _ _}) ⇒ _) ≈N
      (@PointwiseProductN _ _ SetCat_HasProduct _ _ _ _
        (VertexNerveN F) (VertexNerveN G) ∘Nv VertexNerveProductN T U)
  := vertex_nerve_product_natural F G.

End Products.

(** Terminal comparison also keeps value carrier and equality independent. *)

(** 终比较同样保持值载体及相等的独立性。 *)

Section Terminal.
Universes u p.
Constraint u < p.

Definition low_eq_terminal_iso
  : (Nᵥ(VertexTerminalObjectsF) :
      Functor (Δ^op) SetCat@{p u _ _ _ _ _}) ≅N
      ConstF (Δ^op) UnitS@{p u}
  := vertex_nerve_terminal_iso.

Definition high_eq_terminal_iso
  : (Nᵥ(VertexTerminalObjectsF) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      ConstF (Δ^op) UnitS@{u p}
  := vertex_nerve_terminal_iso.

End Terminal.
