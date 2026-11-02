From Cats Require Export Cat.Shape Cat.Diagram.Free.
From Cats Require Import Cat.Core Cat.Functor Cat.Natural.

(** * Cospan Diagrams *)
Definition CospanOb {C : Cat} (X Y Z : @Ob C) (v : CospanVertex) : @Ob C :=
  match v with
  | cospan_left => X
  | cospan_right => Y
  | cospan_tip => Z
  end.

Program Definition cospan_edge_resp {C : Cat} {X Y Z : @Ob C}
    (f : Hom X Z) (g : Hom Y Z) (x y : CospanVertex)
  : @EdgeSet CospanGraph x y →r HomSet (CospanOb X Y Z x) (CospanOb X Y Z y) :=
  {| func e := _ |}.
Next Obligation.
  destruct x, y; cbn in *; destruct e; assumption.
Defined.
Next Obligation.
  intros e e' H. destruct x, y; cbn in *; destruct e, e'; reflexivity.
Defined.

Program Definition CospanGraphMap {C : Cat} {X Y Z : @Ob C}
    (f : Hom X Z) (g : Hom Y Z) : CospanGraph →G UnderlyingGraph C :=
  {| vertex_map := CospanOb X Y Z; edge_map x y := cospan_edge_resp f g x y |}.

Definition CospanDiagram {C : Cat} {X Y Z : @Ob C} (f : Hom X Z) (g : Hom Y Z)
  : Functor CospanShape C := FreeF (CospanGraphMap f g).

Notation "'⟨' f '→←' g '⟩D'" := (CospanDiagram f g) : cat_scope.

Definition CospanConeOver {C : Cat} {D : Functor CospanShape C} {P : @Ob C}
    (p : Hom P (D cospan_left)) (q : Hom P (D cospan_right))
    (H : fmap D (path_edge cospan_l) ∘ p ≈ fmap D (path_edge cospan_r) ∘ q)
  : P ⇒Δ D.
Proof.
  refine (@FreeCone CospanGraph C D P
    (λ v, match v as w return Hom P (D w) with
    | cospan_left => p
    | cospan_right => q
    | cospan_tip => fmap D (path_edge cospan_l) ∘ p
    end) _).
  intros x y e. destruct x, y; cbn in *; destruct e.
  - reflexivity.
  - symmetry. exact H.
Defined.

Definition CospanCone {C : Cat} {X Y Z P : @Ob C}
    {f : Hom X Z} {g : Hom Y Z} (p : Hom P X) (q : Hom P Y)
    (H : f ∘ p ≈ g ∘ q) : P ⇒Δ ⟨f →← g⟩D :=
  @CospanConeOver C (CospanDiagram f g) P p q H.

Lemma cospan_cone_comm {C : Cat} {D : Functor CospanShape C} {P : @Ob C}
    (κ : P ⇒Δ D)
  : fmap D (path_edge cospan_l) ∘ κ cospan_left ≈
      fmap D (path_edge cospan_r) ∘ κ cospan_right.
Proof.
  transitivity (κ cospan_tip).
  - exact (free_cone_edge κ cospan_l).
  - symmetry. exact (free_cone_edge κ cospan_r).
Qed.

(** * Spans by Duality *)
Definition SpanDiagram {C : Cat} {X Y Z : @Ob C} (f : Hom Z X) (g : Hom Z Y)
  : Functor SpanShape C := FromDoubleOpF ∘F OpF (CospanDiagram (C := C^op) f g).

Notation "'⟨' f '←→' g '⟩D'" := (SpanDiagram f g) : cat_scope.
