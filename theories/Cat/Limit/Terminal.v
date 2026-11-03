From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal
  Cat.Limit.Core.
From Cats Require Import
  Cat.Adjunction
  Cat.Limit.Preservation.
From Cats Require Export Cat.Diagram.Discrete.

(** * Terminal Objects as Limits of Empty Diagrams *)

(** * 终对象作为空图式的极限 *)

Section EmptyLimits.
Context {C : Cat} {D : Functor EmptyShape C} {T : @Ob C} (κ : T ⇒Δ D).

(** A terminal object supplies the limiting cone on any empty diagram. *)

(** 终对象给出任意空图式的极限锥。 *)

Definition terminal_empty_limit (HT : is_terminal T)
  : is_limit κ.
Proof.
  intros X μ. destruct (HT X) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - intros [].
  - intros k _. exact (@that _ _ _ _ _ Hh k I).
Defined.

(** The apex of an empty-diagram limit is terminal. *)

(** 空图式极限的顶点是终对象。 *)

Definition empty_limit_terminal (Hκ : is_limit κ)
  : is_terminal T.
Proof.
  intros X. destruct (Hκ X (EmptyCone X)) as [h Hh].
  exists h. refine {|this := I
                   ; that := _
                   |}.
  intros k _. apply (@that _ _ _ _ _ Hh). intros [].
Defined.

(** Terminality is equivalent to the empty-diagram limiting property. *)

(** 终性等价于空图式的极限性质。 *)

Theorem terminal_iff_empty_limit
  : is_terminal T ↔ is_limit κ.
Proof. split; [apply terminal_empty_limit | apply empty_limit_terminal]. Defined.

End EmptyLimits.

(** Select the limit of a empty diagram using the chosen terminal object
    structure. *)

(** 用选定终对象结构选择空图式的极限。 *)

Program Definition TerminalDiagramLimit {C : Cat} `{HT : !HasTerminal C}
    (D : Functor EmptyShape C)
  : HasLimit C D
  :=
  {|Lim := 1
  ; limit_cone := EmptyCone 1
  |}.
Next Obligation. apply terminal_empty_limit. exact terminal_universal. Defined.

(** Choose limits of all empty diagrams from the selected terminal object
    structure. *)

(** 由选定终对象结构选择全部空图式的极限。 *)

Program Definition TerminalLimits {C : Cat} `{HT : !HasTerminal C}
  : HasLimitsOfShape C EmptyShape
  :=
  {|hasLimit := TerminalDiagramLimit
  |}.

(** Recover selected terminal objects from limits of the empty shape. *)

(** 由空形状的极限恢复选定终对象。 *)

Program Definition EmptyLimitsTerminal {C : Cat}
    `{HL : !HasLimitsOfShape C EmptyShape}
  : HasTerminal C
  :=
  {|Term := lim (EmptyDiagram C)
  |}.
Next Obligation.
  exact (empty_limit_terminal (πlim[EmptyDiagram C]) (limit_universal (EmptyDiagram C))).
Defined.

(** A right adjoint preserves the candidate terminal object universal
    property. *)

(** 右伴随保持候选终对象的泛性质。 *)

Definition right_adjoint_preserves_terminal {C D : Cat}
    {F : Functor C D} {G : Functor D C} (A : F ⊣ G)
    {T : @Ob D} (HT : is_terminal T)
  : is_terminal (G T)
  := empty_limit_terminal (MapCone G (@EmptyCone D (EmptyDiagram D) T))
    (right_adjoint_preserves_limit A
      (terminal_empty_limit (@EmptyCone D (EmptyDiagram D) T) HT)).
