From Cats Require Export
  Cat.Binoidal.Center
  Cat.Natural.

(** * Bifunctors and Separate Tensoring *)

(** * 双函子与分别张量 *)

(** The left bracketing of a tensor on triples. *)

(** 三个对象上的左括号张量函子。 *)

Definition TensorLeftF {C : Cat} (T : Fct (C ×C C) C)
  : Fct ((C ×C C) ×C C) C
  := T ∘F (T ×F IdF).

(** The right bracketing, on the same triple-product source. *)

(** 在同一个三重乘积来源上的右括号张量函子。 *)

Program Definition TensorRightF {C : Cat} (T : Fct (C ×C C) C)
  : Fct ((C ×C C) ×C C) C
  :=
  {|F0 p := T (fst (fst p), T (snd (fst p), snd p))
  ; F1 p q f := fmap T
      (X := (fst (fst p), T (snd (fst p), snd p)))
      (Y := (fst (fst q), T (snd (fst q), snd q)))
      (fst (fst f), fmap T
        (X := (snd (fst p), snd p)) (Y := (snd (fst q), snd q))
        (snd (fst f), snd f))
  |}.
Next Obligation.
  intros [[f g] h] [[f' g'] h'] [[Hf Hg] Hh]. cbn.
  apply functor_fmap_proper. split; [exact Hf |].
  exact (@functor_fmap_proper _ _ T
    (snd (fst X), snd X) (snd (fst Y), snd Y)
    (g, h) (g', h') (Hg, Hh)).
Defined.
Next Obligation.
  transitivity (fmap T
    (X := (fst (fst X), T (snd (fst X), snd X)))
    (Y := (fst (fst X), T (snd (fst X), snd X))) (id, id)).
  - apply functor_fmap_proper. split; [reflexivity |].
    exact (@functor_id _ _ T (snd (fst X), snd X)).
  - apply functor_id.
Defined.
Next Obligation.
  etransitivity; [| apply functor_comp].
  apply functor_fmap_proper. split; [reflexivity |].
  exact (@functor_comp _ _ T
    (snd (fst X), snd X) (snd (fst Y), snd Y) (snd (fst Z), snd Z)
    (snd (fst f), snd f) (snd (fst g), snd g)).
Defined.

(** ** Separate Actions from a Bifunctor

    Fix a tensor bifunctor on a category. Recover its two separate actions
    and compare their assembled map with the supplied bifunctor action. *)

(** ** 从双函子得到分别作用

    固定范畴上的张量双函子，恢复两个分别作用，并将组装映射与原双函子作用比较。 *)

Section Bifunctor.
Context {C : Cat} (T : Fct (C ×C C) C).

(** Reuse the same object tensor, fixing one identity arrow at a time. *)

(** 复用同一对象张量，每次固定一侧恒等态射。 *)

Program Definition BifunctorBinoidal
  : BinoidalCat C
  :=
  {|binoidal_tensor X Y := T (X, Y)
  ; binoidal_left X Y Z f := fmap T (X := (Z, X)) (Y := (Z, Y)) (id, f)
  ; binoidal_right X Y Z f := fmap T (X := (X, Z)) (Y := (Y, Z)) (f, id)
  |}.
Next Obligation.
  intros f g H. apply functor_fmap_proper. split; [reflexivity | exact H].
Defined.
Next Obligation.
  intros f g H. apply functor_fmap_proper. split; [exact H | reflexivity].
Defined.
Next Obligation. apply functor_id. Defined.
Next Obligation. apply functor_id. Defined.
Next Obligation.
  rewrite <- functor_comp. apply functor_fmap_proper.
  split; [symmetry; apply comp_id_l | reflexivity].
Defined.
Next Obligation.
  rewrite <- functor_comp. apply functor_fmap_proper.
  split; [reflexivity | symmetry; apply comp_id_l].
Defined.

(** Both execution orders agree by bifunctoriality alone. *)

(** 仅由双函子性，两种执行次序相等。 *)

Definition bifunctor_arrow_central {X Y : @Ob C} (f : Hom X Y)
  : @is_central C BifunctorBinoidal X Y f.
Proof.
  intros Z W g. split.
  - change (fmap T (X := (X, W)) (Y := (Y, W)) (f, id) ∘
      fmap T (X := (X, Z)) (Y := (X, W)) (id, g) ≈
      fmap T (X := (Y, Z)) (Y := (Y, W)) (id, g) ∘
      fmap T (X := (X, Z)) (Y := (Y, Z)) (f, id)).
    rewrite <- !functor_comp.
    apply functor_fmap_proper. split; rewrite comp_id_l, comp_id_r;
      reflexivity.
  - change (fmap T (X := (W, X)) (Y := (W, Y)) (id, f) ∘
      fmap T (X := (Z, X)) (Y := (W, X)) (g, id) ≈
      fmap T (X := (Z, Y)) (Y := (W, Y)) (g, id) ∘
      fmap T (X := (Z, X)) (Y := (Z, Y)) (id, f)).
    rewrite <- !functor_comp.
    apply functor_fmap_proper. split; rewrite comp_id_l, comp_id_r;
      reflexivity.
Defined.

(** Ordered context actions recover the given bifunctor's arrow map
    in specified hom equality, without equality of functor records. *)

(** 有序上下文作用在指定 Hom 相等下恢复给定双函子的态射映射，不比较函子记录。 *)

Lemma bifunctor_sequence {X X' Y Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : @binoidal_sequence C BifunctorBinoidal X X' Y Y' f g ≈
      fmap T (X := (X, Y)) (Y := (X', Y')) (f, g).
Proof.
  change (fmap T (X := (X', Y)) (Y := (X', Y')) (id, g) ∘
    fmap T (X := (X, Y)) (Y := (X', Y)) (f, id) ≈
    fmap T (X := (X, Y)) (Y := (X', Y')) (f, g)).
  rewrite <- functor_comp. apply functor_fmap_proper.
  split; [apply comp_id_l | apply comp_id_r].
Qed.

End Bifunctor.
