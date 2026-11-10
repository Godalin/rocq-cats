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

Program Definition VertexPresentationProduct
    (P Q : VertexPresentation@{x e o h p l a b})
  : VertexPresentation@{x e o h p l a b}
  :=
  {|vertex_labels := vertex_labels P ×S vertex_labels Q
  ; vertex_ambient := vertex_ambient P ×C vertex_ambient Q
  ; vertex_action := VertexProductObjectsF P Q
  |}.

(** The diagram correspondence supplies both projections and uniqueness
    for presentation maps; the maps themselves retain transport. *)

(** 图式对应给出呈现映射的两个投影方程及唯一性，映射本身保留运输。 *)

Definition vertex_presentation_product_universal
    (P Q : VertexPresentation@{x e o h p l a b})
  : is_product
      (C := VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _})
      P Q (VertexPresentationProduct P Q) (VertexFstF P Q) (VertexSndF P Q).
Proof.
  intros R F G. exists (VertexPairF P Q F G). split.
  - exact (snd (vertex_diagram_product_iso P Q (VertexCat R)).2.2
      ((F : Functor (VertexCat R) (VertexCat P)),
       (G : Functor (VertexCat R) (VertexCat Q)))).
  - intros K [H1 H2].
    transitivity (VertexPairF P Q
      (VertexFstF P Q ∘Fᵥ K) (VertexSndF P Q ∘Fᵥ K)).
    + symmetry.
      exact (fst (vertex_diagram_product_iso P Q (VertexCat R)).2.2
        (K : Functor (VertexCat R) (VertexCat (VertexPresentationProduct P Q)))).
    + apply vertex_pair_proper; assumption.
Defined.

(** This chosen structure is available only when explicitly enabled. *)

(** 此选定结构仅在显式启用时可用。 *)

Program Definition VertexPresentationCat_HasProduct
  : HasProduct
      VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
  :=
  {|Prod := VertexPresentationProduct
  ; π1 P Q := VertexFstF P Q
  ; π2 P Q := VertexSndF P Q
  ; product_universal := vertex_presentation_product_universal
  |}.

(** The singleton action is bundled independently at every native size. *)

(** 单元素作用在每个原生大小中独立捆绑。 *)

Program Definition VertexPresentationTerminal
  : VertexPresentation@{x e o h p l a b}
  :=
  {|vertex_labels := UnitS@{x e}
  ; vertex_ambient := CodiscreteCat@{o h p l} unit
  ; vertex_action := VertexTerminalObjectsF@{x e o h p l a b}
  |}.

(** The existing unique terminal map proves terminality of the bundle. *)

(** 已有的唯一终映射证明捆绑对象的终性。 *)

Definition vertex_presentation_terminal_universal
  : is_terminal
      (C := VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _})
      VertexPresentationTerminal.
Proof.
  intros P. exists (VertexTerminalF P). split; [exact I |].
  intros F _. apply vertex_terminal_unique.
Defined.

(** Chosen terminal presentations also require explicit enabling. *)

(** 选定终呈现也要求显式启用。 *)

Program Definition VertexPresentationCat_HasTerminal
  : HasTerminal
      VertexPresentationCat@{x e o h p l a b _ _ _ _ _ _ _ _ _ _}
  :=
  {|Term := VertexPresentationTerminal
  ; terminal_universal := vertex_presentation_terminal_universal
  |}.

End FiniteProducts.
