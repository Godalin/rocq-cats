From Cats Require Export Cat.Preorder.

(** * The Walking Arrow and Commuting Square *)
Definition BoolLe (x y : bool)
  : Type
  := match x, y with true, false => Empty_set | _, _ => unit end.

Program Instance BoolLe_PreOrder
  : PreOrder BoolLe
  := {| PreOrder_Reflexive := _; PreOrder_Transitive := _ |}.
Next Obligation. intros []; exact tt. Defined.
Next Obligation. intros [] [] [] H K; cbn in *; try (destruct H); try (destruct K); exact tt. Defined.

Definition ArrowShape
  := PreorderCat BoolLe.
Definition arrow_step
  : (@Hom ArrowShape) false true
  := tt.

Definition SquareShape
  := ArrowShape ×C ArrowShape.
Definition square_top
  : (@Hom SquareShape) (false, false) (false, true)
  := (tt, tt).
Definition square_left
  : (@Hom SquareShape) (false, false) (true, false)
  := (tt, tt).
Definition square_right
  : (@Hom SquareShape) (false, true) (true, true)
  := (tt, tt).
Definition square_bottom
  : (@Hom SquareShape) (true, false) (true, true)
  := (tt, tt).

Lemma square_comm
  : @HomEq SquareShape _ _
    (square_right ∘ square_top) (square_bottom ∘ square_left).
Proof. split; exact tt. Defined.

(** Both directions exist, and their composites are the unique endomorphisms. *)
Definition IsoShape
  := CodiscreteCat bool.

Definition walking_iso
  : false ≅[IsoShape] true
  := codiscrete_iso false true.
