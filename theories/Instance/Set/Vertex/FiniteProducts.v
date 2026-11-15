From Cats Require Export
  Instance.Set.Vertex.Category
  Instance.Set.Vertex.Product
  Instance.Set.Vertex.Terminal.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Product.Core
  Cat.Terminal
  Cat.Preorder.

(** * Chosen Finite Products of Specified Presentations *)

(** * 指定呈现的选定有限积 *)

Section FiniteProducts.
Universes x e o h p l a b.

(** Bundle the existing componentwise product action at the native sizes. *)

(** 在原生大小中捆绑已有逐分量积作用。 *)

Program Definition VtxPresentationProduct
    (P Q : VtxPresentation@{x e o h p l a b})
  : VtxPresentation@{x e o h p l a b}
  :=
  {|vertex_labels := vertex_labels P ×S vertex_labels Q
  ; vertex_ambient := vertex_ambient P ×C vertex_ambient Q
  ; vertex_action := VtxProductObjF P Q
  |}.

(** The diagram correspondence supplies both projections and uniqueness
    for presentation maps; the maps themselves retain transport. *)

(** 图式对应给出呈现映射的两个投影方程及唯一性，映射本身保留运输。 *)

Definition vertex_presentation_product_universal
    (P Q : VtxPresentation@{x e o h p l a b})
  : is_product
      (C := VtxPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _})
      P Q (VtxPresentationProduct P Q) (VtxFstF P Q) (VtxSndF P Q).
Proof.
  intros R F G. exists (VtxPairF P Q F G). split.
  - exact (snd (vertex_diagram_product_iso P Q (VtxCat R)).2.2
      ((F : Fct (VtxCat R) (VtxCat P)),
       (G : Fct (VtxCat R) (VtxCat Q)))).
  - intros K [H1 H2].
    transitivity (VtxPairF P Q
      (VtxFstF P Q ∘Fᵥ K) (VtxSndF P Q ∘Fᵥ K)).
    + symmetry.
      exact (fst (vertex_diagram_product_iso P Q (VtxCat R)).2.2
        (K : Fct (VtxCat R) (VtxCat (VtxPresentationProduct P Q)))).
    + apply vertex_pair_proper; assumption.
Defined.

(** This chosen structure is available only when explicitly enabled. *)

(** 此选定结构仅在显式启用时可用。 *)

Program Definition VtxPresentationCat_HasProduct
  : HasProduct
      VtxPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
  :=
  {|Prod := VtxPresentationProduct
  ; π1 P Q := VtxFstF P Q
  ; π2 P Q := VtxSndF P Q
  ; product_universal := vertex_presentation_product_universal
  |}.

(** The singleton action is bundled independently at every native size. *)

(** 单元素作用在每个原生大小中独立捆绑。 *)

Program Definition VtxPresentationTerminal
  : VtxPresentation@{x e o h p l a b}
  :=
  {|vertex_labels := UnitS@{x e}
  ; vertex_ambient := CodiscreteCat@{o h p l} unit
  ; vertex_action := VtxTerminalObjF@{x e o h p l a b}
  |}.

(** The existing unique terminal map proves terminality of the bundle. *)

(** 已有的唯一终映射证明捆绑对象的终性。 *)

Definition vertex_presentation_terminal_universal
  : is_terminal
      (C := VtxPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _})
      VtxPresentationTerminal.
Proof.
  intros P. exists (VtxTerminalF P). split; [exact I |].
  intros F _. apply vertex_terminal_unique.
Defined.

(** Chosen terminal presentations also require explicit enabling. *)

(** 选定终呈现也要求显式启用。 *)

Program Definition VtxPresentationCat_HasTerminal
  : HasTerminal
      VtxPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
  :=
  {|Term := VtxPresentationTerminal
  ; terminal_universal := vertex_presentation_terminal_universal
  |}.

End FiniteProducts.
