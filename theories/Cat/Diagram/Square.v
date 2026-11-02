From Cats Require Export Cat.Diagram.Arrow.
From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Functor.Uncurry.

(** * Commuting Squares

    The square is a product of walking arrows. Uncurrying packages its
    commuting equation as the naturality of a transformation of arrows. *)

(** * 交换方形

    方形是步行箭头的乘积；去柯里化把交换方程组织为箭头之间变换的自然性。 *)

Definition SquareDiagram {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : Functor SquareShape C
  := (ArrowDiagram (C := Fct ArrowShape C)
    (@ArrowN C (ArrowDiagram f) (ArrowDiagram k) g h H))^uncF.

Notation "'⟨' f ',' g ';' h ',' k '|' H '⟩□'" := (SquareDiagram f g h k H) : cat_scope.

(** The square diagram sends its top generator to the supplied top arrow. *)

(** 方形图式将上生成边送到给定上边箭头。 *)

Lemma square_diagram_top {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : fmap (SquareDiagram f g h k H) square_top ≈ f.
Proof. cbn. apply comp_id_r. Qed.

(** The square diagram sends its left generator to the supplied left arrow. *)

(** 方形图式将左生成边送到给定左边箭头。 *)

Lemma square_diagram_left {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : fmap (SquareDiagram f g h k H) square_left ≈ g.
Proof. cbn. apply comp_id_l. Qed.

(** The square diagram sends its right generator to the supplied right arrow. *)

(** 方形图式将右生成边送到给定右边箭头。 *)

Lemma square_diagram_right {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : fmap (SquareDiagram f g h k H) square_right ≈ h.
Proof. cbn. apply comp_id_l. Qed.

(** The square diagram sends its bottom generator to the supplied bottom
    arrow. *)

(** 方形图式将下生成边送到给定下边箭头。 *)

Lemma square_diagram_bottom {C : Cat} {A B D E : @Ob C}
    (f : Hom A B) (g : Hom A D) (h : Hom B E) (k : Hom D E)
    (H : h ∘ f ≈ k ∘ g)
  : fmap (SquareDiagram f g h k H) square_bottom ≈ k.
Proof. cbn. apply comp_id_r. Qed.
