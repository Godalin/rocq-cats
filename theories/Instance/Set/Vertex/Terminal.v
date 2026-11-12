From Cats Require Export
  Instance.Set.Vertex.Functor
  Instance.Set.Terminal.
From Cats Require Import
  Cat.Core
  Instance.Set.Core
  Cat.Preorder
  Cat.Diagram.Core.

(** * The Terminal Vertex Presentation

    A singleton label set and the codiscrete singleton category select
    the terminal presentation. This specifies the label equality too;
    terminality of an ambient category alone would not select it. *)

(** * 终顶点呈现

    单元素标签广集与单元素余离散范畴选出终呈现，同时指定标签相等；仅有环境
    范畴的终性并不会选出这些标签数据。 *)

(** All labels and arrows are the singleton's chosen element. The label,
    ambient object, arrow, equality and auxiliary law sizes are independent;
    the same construction inhabits every native presentation profile. *)

(** 全部标签及箭头均为单元素广集的选定元素。标签、环境对象、箭头、相等及
    辅助定律大小相互独立，同一构造适用于每个原生呈现配置。 *)

Definition VertexTerminalObjectsF@{x e o h p l a b}
  : Functor@{x e Set e a b o h p l}
      (EqGpd@{x e e} UnitS@{x e}) (CodiscreteCat@{o h p l} unit)
  := ConstF (EqGpd UnitS@{x e}) (C := CodiscreteCat unit) tt.

(** ** Terminal Diagrams at Independent Sizes

    Keep vertex, category, hom and equality universes independent. Construct
    the terminal presentation functor and compare its diagram setoid with the
    singleton setoid. *)

(** ** 独立大小下的终图式

    保持顶点、范畴、Hom 及相等宇宙独立，构造终呈现函子，并将其图式广集与单元素广集比较。 *)

Section TerminalSizes.
Universes x e o h p l a b.

(** Every presentation admits a transport-preserving terminal map. *)

(** 每个呈现都具有保运输的终映射。 *)

Program Definition VertexTerminalF {X : SetC} {C : Cat}
    (T : Functor (EqGpd X) C)
  : T →ᵥ VertexTerminalObjectsF@{x e o h p l a b}
  :=
  {|vertex_functor := ConstF (VertexCat T)
      (C := VertexCat VertexTerminalObjectsF@{x e o h p l a b}) tt
  |}.
Next Obligation. intros x y p. exact tt. Defined.
Next Obligation. exact tt. Defined.

(** Any two terminal-presentation diagrams are equal in specified label
    and arrow equality, for every source category. *)

(** 对任意源范畴，两个终呈现图式在指定标签与箭头相等下均相等。 *)

Lemma vertex_diagram_terminal_eq {J : Cat}
    (F G : Functor J (VertexCat VertexTerminalObjectsF@{x e o h p l a b}))
  : VertexDiagramEq VertexTerminalObjectsF@{x e o h p l a b} F G.
Proof. exists (λ i, tt). intros i j f. exact tt. Defined.

(** The terminal presentation map is unique in prescribed comparison. *)

(** 终呈现映射在指定比较下唯一。 *)

Lemma vertex_terminal_unique {X : SetC} {C : Cat}
    {T : Functor (EqGpd X) C}
    (F : T →ᵥ VertexTerminalObjectsF@{x e o h p l a b})
  : VertexFunctorEq F (VertexTerminalF T).
Proof. apply vertex_diagram_terminal_eq. Defined.

(** Extract the unique value of a terminal-presentation diagram. *)

(** 提取终呈现图式的唯一值。 *)

Program Definition vertex_diagram_terminal_resp (J : Cat)
  : VertexDiagramS VertexTerminalObjectsF@{x e o h p l a b} J →r UnitS
  :=
  {|func F := tt
  |}.
Next Obligation. intros F G H. exact tt. Defined.

(** The constant singleton diagram is a transparent inverse. *)

(** 常值单元素图式给出透明逆。 *)

Program Definition vertex_diagram_terminal_inv_resp (J : Cat)
  : UnitS →r VertexDiagramS VertexTerminalObjectsF@{x e o h p l a b} J
  :=
  {|func x := ConstF J
      (C := VertexCat VertexTerminalObjectsF@{x e o h p l a b}) tt
  |}.
Next Obligation. intros x y H. apply vertex_diagram_terminal_eq. Defined.

(** Terminal-presentation diagrams recover the terminal setoid at native
    sizes, with no choice or equality of functor fields. *)

(** 终呈现图式在原生大小中恢复终广集，不使用选择或函子字段相等。 *)

Definition vertex_diagram_terminal_iso (J : Cat)
  : VertexDiagramS VertexTerminalObjectsF@{x e o h p l a b} J ≅[SetCat] UnitS.
Proof.
  exists (vertex_diagram_terminal_resp J),
    (vertex_diagram_terminal_inv_resp J). split.
  - intros F. apply vertex_diagram_terminal_eq.
  - intros x. exact tt.
Defined.

End TerminalSizes.
