From Cats Require Import Cat.Core Cat.Functor Cat.Natural Cat.Terminal Cat.Limit.
From Cats Require Import Cat.Adjunction Cat.Limit.Preservation.
From Cats Require Export Cat.Diagram.Discrete.

(** * Terminal Objects as Limits of Empty Diagrams *)
Section EmptyLimits.
Context {C : Cat} {D : Functor EmptyShape C} {T : @Ob C} (κ : T ⇒Δ D).

Definition terminal_empty_limit (HT : is_terminal T) : is_limit κ.
Proof.
  intros X μ. destruct (HT X) as [h Hh].
  exists h. refine {| this := _; that := _ |}.
  - intros [].
  - intros k _. exact (@that _ _ _ _ _ Hh k I).
Defined.

Definition empty_limit_terminal (Hκ : is_limit κ) : is_terminal T.
Proof.
  intros X. destruct (Hκ X (EmptyCone X)) as [h Hh].
  exists h. refine {| this := I; that := _ |}.
  intros k _. apply (@that _ _ _ _ _ Hh). intros [].
Defined.

Theorem terminal_iff_empty_limit : is_terminal T ↔ is_limit κ.
Proof. split; [apply terminal_empty_limit | apply empty_limit_terminal]. Defined.

End EmptyLimits.

Program Definition TerminalDiagramLimit {C : Cat} `{HT : !HasTerminal C}
    (D : Functor EmptyShape C) : HasLimit C D :=
  {| Lim := 1; limit_cone := EmptyCone 1 |}.
Next Obligation. apply terminal_empty_limit. exact terminal_universal. Defined.

Program Definition TerminalLimits {C : Cat} `{HT : !HasTerminal C}
  : HasLimitsOfShape C EmptyShape := {| hasLimit := TerminalDiagramLimit |}.

Program Definition EmptyLimitsTerminal {C : Cat} `{HL : !HasLimitsOfShape C EmptyShape}
  : HasTerminal C := {| Term := lim (EmptyDiagram C) |}.
Next Obligation.
  exact (empty_limit_terminal (πlim[EmptyDiagram C]) (limit_universal (EmptyDiagram C))).
Defined.

Definition right_adjoint_preserves_terminal {C D : Cat}
    {F : Functor C D} {G : Functor D C} (A : F ⊣ G)
    {T : @Ob D} (HT : is_terminal T) : is_terminal (G T) :=
  empty_limit_terminal (MapCone G (@EmptyCone D (EmptyDiagram D) T))
    (right_adjoint_preserves_limit A
      (terminal_empty_limit (@EmptyCone D (EmptyDiagram D) T) HT)).
