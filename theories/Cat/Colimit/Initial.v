From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal
  Cat.Adjunction
  Cat.Diagram.Dual
  Cat.Colimit.Core
  Cat.Colimit.Shape
  Cat.Limit.Terminal.
From Cats Require Export
  Cat.Diagram.DualShape.

(** * Initial Objects as Empty Colimits *)

(** * 始对象作为空余极限 *)

Section EmptyColimits.
Context {C : Cat} {D : Functor (EmptyShape^op) C} {I : @Ob C}
    (κ : D ⇒∇ I).

(** Initiality gives a colimit of any opposite empty diagram. *)

(** 始性给出任意反空图式的余极限。 *)

Definition initial_empty_colimit (HI : is_initial I)
  : is_colimit κ
  := snd (colimit_iff_opposite_limit κ)
      (terminal_empty_limit (OppositeCone κ) HI).

(** The apex of an empty colimit is initial, by opposite terminality. *)

(** 由反范畴中的终性，空余极限的顶点是始对象。 *)

Definition empty_colimit_initial (Hκ : is_colimit κ)
  : is_initial I
  := empty_limit_terminal (OppositeCone κ)
      (fst (colimit_iff_opposite_limit κ) Hκ).

(** Initiality and the empty-diagram colimit property are equivalent. *)

(** 始性与空图式余极限性质等价。 *)

Theorem initial_iff_empty_colimit
  : is_initial I ↔ is_colimit κ.
Proof. split; [apply initial_empty_colimit | apply empty_colimit_initial]. Defined.

End EmptyColimits.

(** Select an empty colimit from the original opposite terminal limit. *)

(** 从原来的反范畴终对象极限选择空余极限。 *)

Definition InitialDiagramColimit {C : Cat} `{HI : !HasInitial C}
    (D : Functor (EmptyShape^op) C)
  : HasColimit C D
  := @OpShapeDiagramColimit EmptyShape C D
      (@TerminalDiagramLimit (C^op) (@hasOpTerminal C HI)
        (OppositeDiagram D)).

(** Selected initial objects give all opposite-empty-shape colimits. *)

(** 选定始对象给出全部反空形状余极限。 *)

Definition InitialColimits {C : Cat} `{HI : !HasInitial C}
  : HasColimitsOfShape C (EmptyShape^op)
  := @OpShapeColimits EmptyShape C
      (@TerminalLimits (C^op) (@hasOpTerminal C HI)).

(** Recover an initial structure using the original empty-limit recovery. *)

(** 使用原来的空极限恢复构造，得到始对象结构。 *)

Program Definition EmptyColimitsInitial {C : Cat}
    `{HC : !HasColimitsOfShape C (EmptyShape^op)}
  : HasInitial C
  :=
  {|hasOpTerminal := @EmptyLimitsTerminal (C^op)
      (@ColimitsOpShapeLimits EmptyShape C HC)
  |}.

(** Left-adjoint preservation is opposite right-adjoint preservation. *)

(** 左伴随的保持性就是反范畴中右伴随的保持性。 *)

Definition left_adjoint_preserves_initial {C D : Cat}
    {F : Functor C D} {G : Functor D C} (A : F ⊣ G)
    {I : @Ob C} (HI : is_initial I)
  : is_initial (F I)
  := @right_adjoint_preserves_terminal (D^op) (C^op)
      (G^opF) (F^opF) (OpAdjunction A) I HI.
