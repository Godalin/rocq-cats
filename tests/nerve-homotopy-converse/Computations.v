From Cats Require Import
  Instance.Set.Simplicial.Vertex.HomotopyInv
  Instance.Set.Vertex.Ordinal
  Instance.Set.Vertex.Terminal
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Recovery Preserves a Noninvertible Directed Edge

    Use the two points of the ordinal interval as constant functors from
    the terminal presentation. Their transformation has no inverse. Its
    homotopy nevertheless recovers a transformation with these exact labels. *)

(** * 恢复保留不可逆有向边

    将序数区间的两个点作为从终呈现出发的常值函子。它们之间的自然变换没有
    逆，但其同伦仍恢复以这两个原标签为端点的自然变换。 *)

Definition InitialF
  : VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set} →ᵥ
      OrdinalObjectsF 1
  := OrdinalVertexPointF 1 fin_first.

Definition FinalF
  : VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set} →ᵥ
      OrdinalObjectsF 1
  := OrdinalVertexPointF 1 (fin_next fin_first).

Program Definition DirectedN
  : InitialF ⇒ FinalF
  :=
  {|nt x := ordinal_step (n := 1) fin_first
  |}.
Next Obligation. exact tt. Defined.

(** The reverse component would inhabit the empty reverse ordinal hom. *)

(** 反向分量将成为空的反向序数 Hom 的元素。 *)

Example directed_not_invertible
  : (DirectedN ⦂ InitialF ≅N FinalF) → Empty_set.
Proof. intros H. exact (H tt).1. Defined.

Definition DirectedHomotopy
  : SimplicialHomotopy
      (VertexNerveN InitialF :
        (Nᵥ(VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set}) :
          Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}) ⇒ Nᵥ(OrdinalObjectsF 1))
      (VertexNerveN FinalF)
  := VertexNerveHomotopy DirectedN.

(** Recovery has the original functor boundaries, without endpoint casts. *)

(** 恢复具有原函子边界，无需端点类型转换。 *)

Definition RecoveredN
  : InitialF ⇒ FinalF
  := VertexNerveInvHomotopyN DirectedHomotopy.

(** The concrete time witness remains transparent through the full inverse. *)

(** 具体时间见证经过完整逆构造后仍保持透明。 *)

Example recovered_edge_computes
  : RecoveredN tt = ordinal_step (n := 1) fin_first.
Proof. reflexivity. Qed.

(** The recovered transformation also cannot acquire an inverse. *)

(** 恢复的自然变换也不可能获得逆。 *)

Example recovered_not_invertible
  : (RecoveredN ⦂ InitialF ≅N FinalF) → Empty_set.
Proof. intros H. exact (H tt).1. Defined.
