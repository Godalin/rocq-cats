From Cats Require Export
  Cat.Monoidal.Functor.

Local Open Scope monoidal_scope.

(** * Lifting Binary Operations

    A lax monoidal functor lifts any binary operation by its tensorator.
    No unit, pure map, strength or closed structure is needed. *)

(** * 提升二元运算

    Lax 幺半函子通过其 tensorator 提升任意二元运算，不需要单位、纯值映射、
    强度或闭结构。 *)

Section Lifting.
Context {C D : Cat}
    {MC : MonoidalCat C} {MD : MonoidalCat D}
    (L : LaxMonoidalFct MC MD).

(** Combine two images, then apply the image of the operation. *)

(** 先组合两个像，再作用运算的像。 *)

Definition lax_lift2 {X Y Z : @Ob C}
    (f : Hom (@tensor C MC X Y) Z)
  : Hom (@tensor D MD (L X) (L Y)) (L Z)
  := fmap L f ∘ φ₂[L; X; Y].

(** Lifting respects the designated equality of operations. *)

(** 提升保持运算的指定相等。 *)

Global Instance lax_lift2_proper {X Y Z : @Ob C}
  : Proper (HomEq ==> HomEq) (@lax_lift2 X Y Z).
Proof. intros f g H. unfold lax_lift2. rewrite H. reflexivity. Qed.

(** Applying an ordinary map after a lifted operation is functorial. *)

(** 在提升后的运算之后作用通常映射，满足函子性。 *)

Lemma lax_lift2_post {X Y Z W : @Ob C}
    (f : Hom (@tensor C MC X Y) Z) (g : Hom Z W)
  : fmap L g ∘ lax_lift2 f ≈ lax_lift2 (g ∘ f).
Proof. unfold lax_lift2. rewrite <- comp_assoc, <- functor_comp. reflexivity. Qed.

(** Naturality moves ordinary maps on the two inputs inside the lifting. *)

(** 自然性将两个输入上的通常映射移入提升。 *)

Lemma lax_lift2_pre {X Y X' Y' Z : @Ob C}
    (f : Hom (@tensor C MC X' Y') Z)
    (g : Hom X X') (h : Hom Y Y')
  : lax_lift2 f ∘ (@tensor_map D MD _ _ _ _ (fmap L g) (fmap L h)) ≈
      lax_lift2 (f ∘ (@tensor_map C MC _ _ _ _ g h)).
Proof.
  unfold lax_lift2. rewrite comp_assoc, (lax_tensor_natural L g h),
    <- comp_assoc, <- functor_comp. reflexivity.
Qed.

(** A lifted operation can be substituted in the left input. *)

(** 可以在左输入中代入提升后的运算。 *)

Lemma lax_lift2_left {X Y Z U V : @Ob C}
    (f : Hom (@tensor C MC X Y) U)
    (g : Hom (@tensor C MC U Z) V)
  : lax_lift2 g ∘ (@tensor_map D MD _ _ _ _ (lax_lift2 f) id) ≈
      lax_lift2 (g ∘ (@tensor_map C MC _ _ _ _ f id)) ∘
        (@tensor_map D MD _ _ _ _ φ₂[L; X; Y] id).
Proof.
  assert (H : @tensor_map D MD _ _ _ _ (lax_lift2 f) id ≈
      (@tensor_map D MD _ _ _ _ (fmap L f) (fmap L (@id Z))) ∘
        (@tensor_map D MD _ _ _ _ φ₂[L; X; Y] id)).
  { rewrite functor_id, <- tensor_map_comp, comp_id_l.
    reflexivity. }
  rewrite H, <- comp_assoc, (lax_lift2_pre g f id). reflexivity.
Qed.

(** The corresponding substitution in the right input keeps its order. *)

(** 右输入中的对应代入保持原有次序。 *)

Lemma lax_lift2_right {X Y Z U V : @Ob C}
    (f : Hom (@tensor C MC Y Z) U)
    (g : Hom (@tensor C MC X U) V)
  : lax_lift2 g ∘ (@tensor_map D MD _ _ _ _ id (lax_lift2 f)) ≈
      lax_lift2 (g ∘ (@tensor_map C MC _ _ _ _ id f)) ∘
        (@tensor_map D MD _ _ _ _ id φ₂[L; Y; Z]).
Proof.
  assert (H : @tensor_map D MD _ _ _ _ id (lax_lift2 f) ≈
      (@tensor_map D MD _ _ _ _ (fmap L (@id X)) (fmap L f)) ∘
        (@tensor_map D MD _ _ _ _ id φ₂[L; Y; Z])).
  { rewrite functor_id, <- tensor_map_comp, comp_id_l.
    reflexivity. }
  rewrite H, <- comp_assoc, (lax_lift2_pre g id f). reflexivity.
Qed.

(** Lifting preserves any binary associativity diagram, with the chosen
    associators on both sides. The operations may have different types. *)

(** 提升保持任意二元结合图，两侧使用选定结合子；各运算可以具有不同类型。 *)

Lemma lax_lift2_assoc {X Y Z U V T : @Ob C}
    (f : Hom (@tensor C MC X Y) U)
    (g : Hom (@tensor C MC U Z) T)
    (h : Hom (@tensor C MC Y Z) V)
    (k : Hom (@tensor C MC X V) T)
    (H : g ∘ (@tensor_map C MC _ _ _ _ f id) ≈
      k ∘ (@tensor_map C MC _ _ _ _ id h) ∘ (@tensor_assoc C MC X Y Z))
  : lax_lift2 g ∘ (@tensor_map D MD _ _ _ _ (lax_lift2 f) id) ≈
      lax_lift2 k ∘ (@tensor_map D MD _ _ _ _ id (lax_lift2 h)) ∘
        (@tensor_assoc D MD (L X) (L Y) (L Z)).
Proof.
  rewrite lax_lift2_left, lax_lift2_right.
  unfold lax_lift2. rewrite H, functor_comp.
  rewrite !comp_assoc. apply comp_proper; [reflexivity |].
  rewrite <- !comp_assoc. exact (lax_assoc L X Y Z).
Qed.

End Lifting.

Arguments lax_lift2 {_ _ _ _} _ {_ _ _} _.

Notation "'lift₂[' L ';' f ']'" := (lax_lift2 L f) : monoidal_scope.
