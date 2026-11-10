From Cats Require Export
  Instance.Set.Vertex.Terminal
  Instance.Set.Simplicial.Vertex.Functor.
From Cats Require Import
  Cat.Core
  Cat.Natural
  Cat.Diagram.Core.

Local Open Scope nat_scope.

(** * The Vertex Nerve Preserves the Terminal Presentation

    The singleton presentation has the constant singleton simplicial setoid
    as its nerve, up to specified natural isomorphism. Its inverse retains
    an actual constant diagram in each dimension. *)

(** * 顶点 nerve 保持终呈现

    单元素呈现的 nerve 在指定自然同构下等于常值单元素单纯广集。
    其逆在每个维度保留实际的常值图式。 *)

(** The comparison takes the unique value in each dimension. *)

(** 比较在每个维度取唯一值。 *)

Program Definition VertexNerveTerminalN@{u p +}
  : (Nᵥ(VertexTerminalObjectsF) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      ConstF (Δ^op) (C := SetCat@{u p _ _ _ _ _}) UnitS@{u p}
  :=
  {|nt n :=
      {|func x := tt
      |}
  |}.
Next Obligation. intros x y H. exact tt. Defined.
Next Obligation. intros x. exact tt. Defined.

(** The inverse chooses the singleton-labelled constant ordinal diagram. *)

(** 逆选取带单元素标签的常值序数图式。 *)

Program Definition VertexNerveTerminalInvN@{u p +}
  : ConstF (Δ^op) (C := SetCat@{u p _ _ _ _ _}) UnitS@{u p} ⇒
      (Nᵥ(VertexTerminalObjectsF) :
        Functor (Δ^op) SetCat@{u p _ _ _ _ _})
  :=
  {|nt n :=
      {|func x := ⟨ConstF [Ord n] (C := VertexCat VertexTerminalObjectsF) tt⟩ᵥ
      |}
  |}.
Next Obligation.
  intros x y H. refine {|lower := _
                       |}. apply vertex_diagram_terminal_eq.
Defined.
Next Obligation.
  intros x. refine {|lower := _
                    |}. apply vertex_diagram_terminal_eq.
Defined.

(** Both round trips use specified equality, independently of the two
    common value sizes. No functor records or witnesses are identified. *)

(** 两侧往返均使用指定相等，与两个共同值大小相互独立；不识别函子记录或见证。 *)

Definition vertex_nerve_terminal_iso@{u p +}
  : (Nᵥ(VertexTerminalObjectsF) :
      Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ≅N
      ConstF (Δ^op) (C := SetCat@{u p _ _ _ _ _}) UnitS@{u p}.
Proof.
  exists VertexNerveTerminalN. intros n. exists (VertexNerveTerminalInvN n).
  split.
  - intros [F]. refine {|lower := _
                       |}. apply vertex_diagram_terminal_eq.
  - intros x. exact tt.
Defined.

(** The terminal comparison commutes with every presentation map. *)

(** 终比较与每个呈现映射交换。 *)

Lemma vertex_nerve_terminal_natural@{u p +}
    {X : SetC} {Y : SetC} {C : Cat} {D : Cat}
    {T : Functor (EqGpd X) C} {U : Functor (EqGpd Y) D} (F : T →ᵥ U)
  : (VertexNerveTerminalN ∘Nv VertexNerveN (VertexTerminalF U) ∘Nv
      VertexNerveN F :
      (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒ _) ≈N
      (VertexNerveTerminalN ∘Nv VertexNerveN (VertexTerminalF T)).
Proof. intros n x. exact tt. Defined.
