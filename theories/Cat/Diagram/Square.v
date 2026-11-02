From Cats Require Export Cat.Diagram.Arrow.
From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Functor.Uncurry.

(** * Commuting Squares

    The square is a product of walking arrows. Uncurrying packages its
    commuting equation as the naturality of a transformation of arrows. *)
Definition SquareDiagram {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : Functor SquareShape C
  := (ArrowDiagram (C := Fct ArrowShape C)
    (@ArrowN C (ArrowDiagram f) (ArrowDiagram k) g h H))^uncF.

Notation "'⟨' f ',' g ';' h ',' k '|' H '⟩□'" := (SquareDiagram f g h k H) : cat_scope.

Lemma square_diagram_top {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : fmap (SquareDiagram f g h k H) square_top ≈ f.
Proof. cbn. apply comp_id_r. Qed.

Lemma square_diagram_left {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : fmap (SquareDiagram f g h k H) square_left ≈ g.
Proof. cbn. apply comp_id_l. Qed.

Lemma square_diagram_right {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : fmap (SquareDiagram f g h k H) square_right ≈ h.
Proof. cbn. apply comp_id_l. Qed.

Lemma square_diagram_bottom {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : fmap (SquareDiagram f g h k H) square_bottom ≈ k.
Proof. cbn. apply comp_id_r. Qed.
