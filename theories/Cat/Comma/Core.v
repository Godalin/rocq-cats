From Cats Require Export
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Comma Categories

    Two functors into a common category determine commuting squares.
    Equality compares the two side maps, retaining the square witness as
    data. The three categories keep their own native hom universes. *)

(** * 逗号范畴

    两个取值于同一范畴的函子确定交换方形。相等比较两条侧边，方形见证仍作为
    数据保留；三个范畴各自保留原有 Hom 宇宙。 *)

Section CommaData.
Context {A B C : Cat} (F : Fct A C) (G : Fct B C).

(** An arrow from an [F]-image to a [G]-image. Neither endpoint is forgotten. *)

(** 从 [F] 的像到 [G] 的像的箭头，两个端点均保留。 *)

Record CommaOb
  :=
  { comma_left_ob : @Ob A
  ; comma_right_ob : @Ob B
  ; comma_arrow : Hom (F comma_left_ob) (G comma_right_ob)
  }.

(** A pair of side maps whose square commutes in [C]. *)

(** 在 [C] 中构成交换方形的一对侧边映射。 *)

Record CommaHom (X Y : CommaOb)
  :=
  { comma_left : Hom (comma_left_ob X) (comma_left_ob Y)
  ; comma_right : Hom (comma_right_ob X) (comma_right_ob Y)
  ; comma_comm : fmap G comma_right ∘ comma_arrow X ≈
      comma_arrow Y ∘ fmap F comma_left
  }.

Arguments comma_left {_ _} _.
Arguments comma_right {_ _} _.
Arguments comma_comm {_ _} _.

(** Componentwise hom equality does not compare commutativity witnesses. *)

(** 逐分量 Hom 相等不比较交换性见证。 *)

Definition CommaHomEq {X Y : CommaOb} (f g : CommaHom X Y)
  : Type
  := comma_left f ≈ comma_left g ∧ comma_right f ≈ comma_right g.

(** The side-map equalities give reflexivity, symmetry and transitivity. *)

(** 两条侧边的相等给出自反性、对称性和传递性。 *)

Global Instance CommaHomEq_Equivalence {X Y : CommaOb}
  : Equivalence (@CommaHomEq X Y).
Proof.
  split.
  - intros f. split; reflexivity.
  - intros f g [Hl Hr]. split; symmetry; assumption.
  - intros f g h [Hl Hr] [Kl Kr]. split; etransitivity; eassumption.
Defined.

(** The canonical hom-set retains squares and compares their side maps. *)

(** 典范 Hom 广集保留方形，并比较两条侧边。 *)

Program Canonical CommaHomS (X Y : CommaOb)
  : SetC
  :=
  {|carrier := CommaHom X Y
  ; carrier_equiv := CommaHomEq
  ; carrier_setoid := CommaHomEq_Equivalence
  |}.

(** Identity side maps form a commuting square by the functor identity laws. *)

(** 由函子恒等律，恒等侧边构成交换方形。 *)

Program Definition comma_id (X : CommaOb)
  : CommaHom X X
  :=
  {|comma_left := id
  ; comma_right := id
  |}.
Next Obligation.
  rewrite !functor_id, comp_id_l, comp_id_r. reflexivity.
Defined.

(** Paste two squares; only functoriality and associativity are needed. *)

(** 粘合两个方形，只使用函子性与结合律。 *)

Program Definition comma_comp {X Y Z : CommaOb}
    (g : CommaHom Y Z) (f : CommaHom X Y)
  : CommaHom X Z
  :=
  {|comma_left := comma_left g ∘ comma_left f
  ; comma_right := comma_right g ∘ comma_right f
  |}.
Next Obligation.
  rewrite (@functor_comp B C G _ _ _ (comma_right g) (comma_right f)),
    (@functor_comp A C F _ _ _ (comma_left g) (comma_left f)).
  rewrite comp_assoc, (comma_comm f), <- comp_assoc,
    (comma_comm g), comp_assoc. reflexivity.
Defined.

End CommaData.

Arguments comma_left_ob {_ _ _ _ _} _.
Arguments comma_right_ob {_ _ _ _ _} _.
Arguments comma_arrow {_ _ _ _ _} _.
Arguments CommaHom {_ _ _ _ _} _ _.
Arguments comma_left {_ _ _ _ _ _ _} _.
Arguments comma_right {_ _ _ _ _ _ _} _.
Arguments comma_comm {_ _ _ _ _ _ _} _.
Arguments CommaHomEq {_ _ _ _ _ _ _} _ _.
Arguments CommaHomS {_ _ _ _ _} _ _.
Arguments comma_id {_ _ _ _ _} _.
Arguments comma_comp {_ _ _ _ _ _ _ _} _ _.

(** The comma construction is a category with componentwise equations. *)

(** 逗号构造以逐分量方程组成范畴。 *)

Program Definition Comma {A B C : Cat} (F : Fct A C) (G : Fct B C)
  : Cat
  :=
  {|Ob := CommaOb F G
  ; HomSet := CommaHomS
  ; id := comma_id
  ; comp _ _ _ := comma_comp
  |}.
Next Obligation.
  intros g g' [Hl Hr] f f' [Kl Kr]. split; apply comp_proper; assumption.
Defined.
Next Obligation. split; apply comp_id_r. Defined.
Next Obligation. split; apply comp_id_l. Defined.
Next Obligation. split; apply comp_assoc. Defined.

Infix "↓C" := Comma (at level 40, no associativity) : cat_scope.

(** Projection to the left endpoint category. *)

(** 投影到左端点范畴。 *)

Program Definition CommaLeftF {A B C : Cat}
    (F : Fct A C) (G : Fct B C)
  : Fct (F ↓C G) A
  :=
  {|F0 := comma_left_ob
  ; F1 X Y := comma_left
  |}.
Next Obligation. intros f g H. exact (fst H). Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Projection to the right endpoint category. *)

(** 投影到右端点范畴。 *)

Program Definition CommaRightF {A B C : Cat}
    (F : Fct A C) (G : Fct B C)
  : Fct (F ↓C G) B
  :=
  {|F0 := comma_right_ob
  ; F1 X Y := comma_right
  |}.
Next Obligation. intros f g H. exact (snd H). Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** The stored arrows are a natural transformation between the projections. *)

(** 所保存箭头构成两个投影之间的自然变换。 *)

Program Definition CommaSquareN {A B C : Cat}
    (F : Fct A C) (G : Fct B C)
  : (F ∘F CommaLeftF F G) ⇒ (G ∘F CommaRightF F G)
  :=
  {|nt := comma_arrow
  |}.
Next Obligation. symmetry. exact (comma_comm f). Defined.
