From Cats Require Export
  Instance.Set.Vertex.Category
  Instance.Set.Simplicial.Vertex.Reconstruction.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * The Fully Faithful Vertex Nerve Functor

    The nerve now acts on the category of specified object presentations.
    Its object and morphism maps are the existing nerve constructions;
    fullness and faithfulness reuse the transparent reconstruction and its
    two round trips. Common value carrier and equality sizes are separate. *)

(** * 全忠实的顶点 nerve 函子

    nerve 作用于指定对象呈现的范畴。对象及态射映射为已有的 nerve 构造；
    满性及忠实性复用透明重构与两侧往返律。共同值载体及相等大小保持分离。 *)

(** The existing nerve action is a functor, with its identity, composition
    and respectfulness laws in their specified equalities. *)

(** 已有 nerve 作用构成函子，其恒等、复合及保相等定律均使用指定相等。 *)

Program Definition VertexNerveF@{u r x e o h p l a b +}
  : Fct VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
      (FctCat (Δ^op) SetCat@{u r _ _ _ _ _})
  :=
  {|F0 P := Nᵥ(P)
  ; F1 P Q F := VertexNerveN F
  ; functor_fmap_proper P Q F G H := vertex_nerve_proper F G H
  |}.
Next Obligation. exact (vertex_nerve_id X). Defined.
Next Obligation. exact (vertex_nerve_comp f g). Defined.

(** Every simplicial map between image nerves has the existing reconstructed
    presentation morphism as a chosen preimage. *)

(** 像 nerve 之间的每个单纯映射，都以已有重构呈现态射作为选定原像。 *)

Definition vertex_nerve_full@{u r x e o h p l a b +}
  : is_full (VertexNerveF :
      Fct VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
        (FctCat (Δ^op) SetCat@{u r _ _ _ _ _})).
Proof.
  intros P Q α. exists (VertexNerveInvF α). exact (vertex_nerve_β α).
Defined.

(** Reconstruction respects equality and its other round trip reflects
    equality of presentation morphisms. *)

(** 重构保持相等，且另一侧往返律反映呈现态射的相等。 *)

Definition vertex_nerve_faithful@{u r x e o h p l a b +}
  : is_faithful (VertexNerveF :
      Fct VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
        (FctCat (Δ^op) SetCat@{u r _ _ _ _ _})).
Proof.
  intros P Q F G H.
  transitivity (VertexNerveInvF (VertexNerveN F)).
  - symmetry. apply vertex_nerve_η.
  - transitivity (VertexNerveInvF (VertexNerveN G)).
    + apply vertex_nerve_inv_proper. exact H.
    + apply vertex_nerve_η.
Defined.

(** Full faithfulness is expressed by the general functor interface, rather
    than only by a separate hom correspondence. The fullness witness keeps
    the computable inverse reconstruction. *)

(** 全忠实性使用通用函子接口表达，不仅是单独的 Hom 对应；满性见证保留可计算
    的反向重构。 *)

Definition vertex_nerve_fully_faithful@{u r x e o h p l a b +}
  : is_fully_faithful (VertexNerveF :
      Fct VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
        (FctCat (Δ^op) SetCat@{u r _ _ _ _ _}))
  := (vertex_nerve_full, vertex_nerve_faithful).
