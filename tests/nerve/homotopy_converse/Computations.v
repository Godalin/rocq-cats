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

Definition InitialF
  : VtxTerminalObjF@{Set Set Set Set Set Set Set Set} →ᵥ
      OrdinalObjF 1
  := OrdinalVtxPointF 1 fin_first.

Definition FinalF
  : VtxTerminalObjF@{Set Set Set Set Set Set Set Set} →ᵥ
      OrdinalObjF 1
  := OrdinalVtxPointF 1 (fin_next fin_first).

Program Definition DirectedN
  : InitialF ⇒ FinalF
  :=
  {|nt x := ordinal_step (n := 1) fin_first
  |}.
Next Obligation. exact tt. Defined.

(** The reverse component would inhabit the empty reverse ordinal hom. *)

Example directed_not_invertible
  : (DirectedN ⦂ InitialF ≅N FinalF) → Empty_set.
Proof. intros H. exact (H tt).1. Defined.

Definition DirectedHomotopy
  : SimplicialHomotopy
      (VtxNerveN InitialF :
        (Nᵥ(VtxTerminalObjF@{Set Set Set Set Set Set Set Set}) :
          Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) ⇒ Nᵥ(OrdinalObjF 1))
      (VtxNerveN FinalF)
  := VtxNerveHomotopy DirectedN.

(** Recovery has the original functor boundaries, without endpoint casts. *)

Definition RecoveredN
  : InitialF ⇒ FinalF
  := VtxNerveInvHomotopyN DirectedHomotopy.

(** The concrete time witness remains transparent through the full inverse. *)

Example recovered_edge_computes
  : RecoveredN tt = ordinal_step (n := 1) fin_first.
Proof. reflexivity. Qed.

(** The recovered transformation also cannot acquire an inverse. *)

Example recovered_not_invertible
  : (RecoveredN ⦂ InitialF ≅N FinalF) → Empty_set.
Proof. intros H. exact (H tt).1. Defined.
