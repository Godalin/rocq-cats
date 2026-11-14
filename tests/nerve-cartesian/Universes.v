From Cats Require Import
  Instance.Set.Simplicial.Vertex.Cartesian
  Cat.Core
  Cat.Natural
  Cat.Terminal
  Cat.Product.Core
  Cat.Functor.Cartesian
  Cat.Functor.FiniteProducts
  Instance.Set.Product
  Instance.Set.Terminal.

(** * Independent Sizes for Chosen Finite Products *)

(** * 选定有限积的独立大小 *)

Section Levels.
Universes e h o l u q.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Constraint l < u.
Constraint u < q.

(** The native arrow carrier is strictly above its equality witnesses. *)

(** 原生箭头载体严格高于其相等见证。 *)

Definition Presentations
  : Cat
  := VertexPresentationCat@{o e o h e l h e _ _ _ _ _ _ _ _ _ _}.

Definition NativeProducts
  : HasProduct Presentations
  := VertexPresentationCat_HasProduct.

Definition NativeTerminal
  : HasTerminal Presentations
  := VertexPresentationCat_HasTerminal.

(** The common value equality is below the category-law bound and carrier. *)

(** 共同值相等低于范畴定律界及载体。 *)

Definition low_eq_cartesian
  : @CartFct Presentations
      (FctCat (Δ^op) SetCat@{u o _ _ _ _ _}) NativeTerminal NativeProducts
  := VertexNerveCartesianF.

(** The same source also permits value equality above its carrier. *)

(** 同一源也允许值相等高于其载体。 *)

Definition high_eq_cartesian
  : @CartFct Presentations
      (FctCat (Δ^op) SetCat@{u q _ _ _ _ _}) NativeTerminal NativeProducts
  := VertexNerveCartesianF.

(** Reverse the native label and arrow carrier/equality profiles. *)

(** 反转原生标签及箭头的载体／相等配置。 *)

Definition ReversePresentations
  : Cat
  := VertexPresentationCat@{e o e h o l o o _ _ _ _ _ _ _ _ _ _}.

Definition ReverseProducts
  : HasProduct ReversePresentations
  := VertexPresentationCat_HasProduct.

Definition ReverseTerminal
  : HasTerminal ReversePresentations
  := VertexPresentationCat_HasTerminal.

Definition reverse_native_cartesian
  : @CartFct ReversePresentations
      (FctCat (Δ^op) SetCat@{u o _ _ _ _ _}) ReverseTerminal ReverseProducts
  := VertexNerveCartesianF.

(** The general pointwise structures retain both strict value-size orders. *)

(** 通用点态结构保留两种严格值大小次序。 *)

Definition low_eq_pointwise_products
  : HasProduct (FctCat (Δ^op) SetCat@{u o _ _ _ _ _})
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

Definition high_eq_pointwise_products
  : HasProduct (FctCat (Δ^op) SetCat@{u q _ _ _ _ _})
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

Definition low_eq_pointwise_terminal
  : HasTerminal (FctCat (Δ^op) SetCat@{u o _ _ _ _ _})
  := @FctCat_HasTerminal _ _ SetCat_HasTerminal.

Definition high_eq_pointwise_terminal
  : HasTerminal (FctCat (Δ^op) SetCat@{u q _ _ _ _ _})
  := @FctCat_HasTerminal _ _ SetCat_HasTerminal.

(** A probe larger than both value sizes does not resize pointwise values. *)

(** 大于两个值大小的探测范畴不要求调整点态值的大小。 *)

Context (J : Cat@{q q q q q}).

Definition large_probe_products
  : HasProduct (FctCat J SetCat@{u o _ _ _ _ _})
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

Definition large_probe_terminal
  : HasTerminal (FctCat J SetCat@{u o _ _ _ _ _})
  := @FctCat_HasTerminal _ _ SetCat_HasTerminal.

End Levels.
