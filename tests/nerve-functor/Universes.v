From Cats Require Import
  Instance.Set.Simplicial.Vertex.Category
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Independent Sizes for the Bundled Nerve Functor

    Compare carrier and equality sizes in both strict orders. Stored action
    laws may have larger auxiliary universes than the bundle's bound; the
    constructor checks those laws pointwise without resizing their data. *)

(** * 捆绑 nerve 函子的独立大小

    分别检查载体及相等大小的两种严格次序。已存作用定律可具有比捆绑界更大的
    辅助宇宙；构造子逐点检查这些定律，而不调整其数据大小。 *)

Section Levels.
Universes e h o l u p.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < p.

(** Value equality strictly below the carrier, with native hom equality
    also below its native arrow carrier. *)

(** 值相等严格低于载体，且原生 Hom 相等也低于其原生箭头载体。 *)

Definition low_eq_nerve_functor
  : Functor
      VertexPresentationCat@{o e o h e l h e _ _ _ _ _ _ _ _ _ _}
      (Fct (Δ^op) SetCat@{u o _ _ _ _ _})
  := VertexNerveF.

(** The same source supports equality strictly above the value carrier. *)

(** 同一源也支持严格高于值载体的相等。 *)

Definition high_eq_nerve_functor
  : Functor
      VertexPresentationCat@{o e o h e l h e _ _ _ _ _ _ _ _ _ _}
      (Fct (Δ^op) SetCat@{u p _ _ _ _ _})
  := VertexNerveF.

(** Reverse both native carrier/equality profiles. *)

(** 反转两个原生载体／相等大小配置。 *)

Definition reverse_native_nerve_functor
  : Functor
      VertexPresentationCat@{e o e h o l o o _ _ _ _ _ _ _ _ _ _}
      (Fct (Δ^op) SetCat@{u o _ _ _ _ _})
  := VertexNerveF.

(** Full faithfulness retains all of these independent sizes. *)

(** 全忠实性保留全部这些独立大小。 *)

Definition low_eq_fully_faithful
  : is_fully_faithful low_eq_nerve_functor
  := vertex_nerve_fully_faithful.

Definition high_eq_fully_faithful
  : is_fully_faithful high_eq_nerve_functor
  := vertex_nerve_fully_faithful.

Definition reverse_native_fully_faithful
  : is_fully_faithful reverse_native_nerve_functor
  := vertex_nerve_fully_faithful.

(** Repack action laws from strictly larger auxiliary bounds, including
    the equality-groupoid law bound, into the chosen presentation bound. *)

(** 将严格更大辅助界中的作用定律重新包装至选定呈现界，包括相等群胚的定律界。 *)

Context (X : SetC@{o e}) (C : Cat@{o h e l l})
    (T : Functor@{o e Set u u p o h e l} (EqGpd@{o e u} X) C).

Definition repacked_large_action_laws
  : VertexPresentation@{o e o h e l h e}
  := VertexPresentationOf T.

End Levels.
