From Cats Require Export Cat.Shape.Discrete Cat.Diagram.Free.
From Cats Require Import Cat.Core Cat.Functor Cat.Natural.

(** * Discrete Diagrams *)
Program Definition DiscreteGraphMap {C : Cat} {V : Type} (D : V → @Ob C)
  : DiscreteGraph V →G UnderlyingGraph C :=
  {| vertex_map := D
   ; edge_map x y := {| func e := match e with end |} |}.
Next Obligation. intros []. Qed.

Definition DiscreteF {C : Cat} {V : Type} (D : V → @Ob C)
  : Functor (DiscreteCat V) C := FreeF (DiscreteGraphMap D).

Definition DiscreteCone {C : Cat} {V : Type} {D : Functor (DiscreteCat V) C}
    {X : @Ob C} (κ : ∀ v, Hom X (D v)) : X ⇒Δ D.
Proof. refine (FreeCone κ _). intros x y []. Defined.

(** False is the left endpoint and true is the right endpoint. *)
Definition PairDiagram {C : Cat} (X Y : @Ob C) : Functor PairShape C :=
  DiscreteF (λ b : bool, if b then Y else X).

Notation "'⟨' X ',' Y '⟩D'" := (PairDiagram X Y) : cat_scope.

Definition PairCone {C : Cat} {X Y P : @Ob C} (p : Hom P X) (q : Hom P Y)
  : P ⇒Δ ⟨X, Y⟩D :=
  @DiscreteCone C bool (PairDiagram X Y) P
    (λ b : bool, if b as v return Hom P (if v then Y else X)
    then q else p).

Notation "'⟨' p ',' q '⟩Cone'" := (PairCone p q) : cat_scope.

(** * Empty and Single-Object Diagrams *)
Definition EmptyDiagram (C : Cat) : Functor EmptyShape C :=
  DiscreteF (λ x : Empty_set, match x with end).

Definition PointDiagram {C : Cat} (X : @Ob C) : Functor PointShape C :=
  DiscreteF (λ _ : unit, X).
