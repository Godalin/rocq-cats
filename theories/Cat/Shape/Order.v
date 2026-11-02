From Cats Require Export Cat.Preorder.

(** * The Walking Arrow and Commuting Square *)

(** * 步行箭头与交换方形 *)

(** The order from false to true, represented by unit or empty witnesses. *)

(** 从 false 到 true 的顺序，见证为单元素或空类型。 *)

Definition BoolLe (x y : bool)
  : Type
  := match x, y with true, false => Empty_set | _, _ => unit end.

(** [BoolLe] is a preorder. *)

(** [BoolLe] 是预序。 *)

Program Instance BoolLe_PreOrder
  : PreOrder BoolLe
  :=
  {|PreOrder_Reflexive := _
  ; PreOrder_Transitive := _
  |}.
Next Obligation. intros []; exact tt. Defined.
Next Obligation. intros [] [] [] H K; cbn in *; try (destruct H); try (destruct K); exact tt. Defined.

(** The walking arrow as a thin preorder category. *)

(** 以薄预序范畴表示的步行箭头。 *)

Definition ArrowShape
  := PreorderCat BoolLe.
(** The generating arrow from false to true. *)

(** 从 false 到 true 的生成箭头。 *)

Definition arrow_step
  : (@Hom ArrowShape) false true
  := tt.

(** The product of two walking-arrow categories. *)

(** 两个步行箭头范畴的乘积。 *)

Definition SquareShape
  := ArrowShape ×C ArrowShape.
(** The top edge of the square shape. *)

(** 方形形状的上边。 *)

Definition square_top
  : (@Hom SquareShape) (false, false) (false, true)
  := (tt, tt).
(** The left edge of the square shape. *)

(** 方形形状的左边。 *)

Definition square_left
  : (@Hom SquareShape) (false, false) (true, false)
  := (tt, tt).
(** The right edge of the square shape. *)

(** 方形形状的右边。 *)

Definition square_right
  : (@Hom SquareShape) (false, true) (true, true)
  := (tt, tt).
(** The bottom edge of the square shape. *)

(** 方形形状的下边。 *)

Definition square_bottom
  : (@Hom SquareShape) (true, false) (true, true)
  := (tt, tt).

(** The two paths around the square are equal in the shape. *)

(** 方形的两条绕行路径在形状中相等。 *)

Lemma square_comm
  : @HomEq SquareShape _ _
    (square_right ∘ square_top) (square_bottom ∘ square_left).
Proof. split; exact tt. Defined.

(** Both directions exist, and their composites are the unique endomorphisms. *)

(** 两个方向的态射都存在，其复合是唯一的自同态射。 *)

Definition IsoShape
  := CodiscreteCat bool.

(** The isomorphism between the two objects of the walking-isomorphism shape. *)

(** 步行同构形状中两个对象之间的同构。 *)

Definition walking_iso
  : false ≅[IsoShape] true
  := codiscrete_iso false true.
