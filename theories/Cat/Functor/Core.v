From Cats Require Import Cat.Core.



(** * Functor *)

(** * 函子 *)

(** Object and respectful morphism maps preserving identity and composition. *)

(** 保持恒等与复合的对象映射及保相等态射映射。 *)

Record Functor (C D : Cat)
  :=
  { F0 :> @Ob C → @Ob D
  ; F1 {X Y : @Ob C} : Hom X Y → Hom (F0 X) (F0 Y)

  ; functor_fmap_proper {X Y}
    :: Proper (@HomEq[X, Y] ==> @HomEq[F0 X, F0 Y]) F1

  ; functor_id {X}
    : F1 (@id X) ≈ @id (F0 X)

  ; functor_comp {X Y Z} (f : Hom Y Z) (g : Hom X Y)
    : F1 (f ∘ g) ≈ F1 f ∘ F1 g
  }.

Notation fmap F := (@F1 _ _ F).

(** ** Faithful and Full Functors

    Comparisons use the source and target categories' morphism equivalences.
    Fullness retains a preimage witness in [Type] for each target morphism. *)

(** ** 忠实函子与满函子

    比较使用两侧范畴指定的态射相等；满性为每条目标态射保留 Type 中的原像见证。 *)

Definition is_faithful {C D : Cat} (F : Functor C D)
  := ∀ X Y (f g : Hom X Y), fmap F f ≈ fmap F g → f ≈ g.

(** Every arrow between image objects has a selected preimage up to hom
    equality. *)

(** 像对象之间的每条箭头都具有按 Hom 相等选取的原像。 *)

Definition is_full {C D : Cat} (F : Functor C D)
  := ∀ X Y (g : Hom (F X) (F Y)), ∃ f : Hom X Y, fmap F f ≈ g.

(** Fullness together with faithfulness, retaining full preimage data. *)

(** 同时具有满性与忠实性，并保留满性的原像数据。 *)

Definition is_fully_faithful {C D : Cat} (F : Functor C D)
  := is_full F ∧ is_faithful F.

(** Essential surjectivity retains an object representative and an
    isomorphism, rather than an equality of objects or a truncated existence
    statement. *)

(** 本质满保留对象代表与同构，不要求对象原生相等，也不截断存在见证。 *)

Definition is_essentially_surjective {C D : Cat} (F : Functor C D)
  := ∀ Y : @Ob D, ∃ X : @Ob C, F X ≅ Y.

(** A functor sends an invertible arrow to an invertible arrow. *)

(** 函子将可逆箭头送到可逆箭头。 *)

Definition functor_is_iso {C D : Cat} (F : Functor C D)
    {X Y : @Ob C} (f : Hom X Y) (Hf : is_iso f)
  : is_iso (fmap F f).
Proof.
  exists (fmap F Hf.1). split;
    unfold is_linv_of, is_rinv_of in *;
    rewrite <- functor_comp;
    [rewrite (fst Hf.2) | rewrite (snd Hf.2)]; apply functor_id.
Defined.



(** ** Identity Functor *)

(** ** 恒等函子 *)

(** The identity functor. *)

(** 恒等函子。 *)

Program Canonical IdF {C : Cat}
  : Functor C C
  :=
  {|F0 X := X
  ; F1 _ _ f := f
  |}.
Next Obligation. intros x y. auto. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** Compose functors on objects and morphisms. *)

(** 在对象与态射上复合函子。 *)

Program Canonical CompF {C D E : Cat}
    (G : Functor D E) (F : Functor C D)
  :=
  {|F0 X := (G (F X))
  ; F1 _ _ f := fmap G (fmap F f)
  |}.
Next Obligation. intros f g H.
  rewrite functor_fmap_proper. reflexivity.
  rewrite functor_fmap_proper. reflexivity. auto.
Qed.
Next Obligation.
  repeat rewrite functor_id. reflexivity.
Qed.
Next Obligation.
  repeat rewrite functor_comp. reflexivity.
Qed.

(** ** Fixing One Argument of a Functor from a Product Category *)

(** ** 固定乘积范畴上的一个函子参数 *)

Section PartialFunctor.
Context {C D E : Cat}.

(** Vary the first argument, keeping the second fixed. *)

(** 改变第一个参数，固定第二个参数。 *)

Program Definition π1F (F : Functor (C ×C D) E) (d : @Ob D)
  : Functor C E
  :=
  {|F0 c := F (c, d)
  ; F1 X Y f := fmap F (X := (X, d)) (Y := (Y, d)) (f, id)
  |}.
Next Obligation.
  intros u v Huv. apply functor_fmap_proper. split; cato.
Qed.
Next Obligation. apply functor_id. Qed.
Next Obligation.
  rewrite <- functor_comp. apply functor_fmap_proper. split; cato.
Qed.

(** Vary the second argument, keeping the first fixed. *)

(** 改变第二个参数，固定第一个参数。 *)

Program Definition π2F (F : Functor (C ×C D) E) (c : @Ob C)
  : Functor D E
  :=
  {|F0 d := F (c, d)
  ; F1 X Y f := fmap F (X := (c, X)) (Y := (c, Y)) (id, f)
  |}.
Next Obligation.
  intros u v Huv. apply functor_fmap_proper. split; cato.
Qed.
Next Obligation. apply functor_id. Qed.
Next Obligation.
  rewrite <- functor_comp. apply functor_fmap_proper. split; cato.
Qed.

End PartialFunctor.

Infix "∘F" := CompF
  (at level 40) : cat_scope.

(** Independent functors act componentwise on a product category. *)

(** 两个独立函子在乘积范畴上逐分量作用。 *)

Program Definition ProdF {C D E K : Cat} (F : Functor C D) (G : Functor E K)
  : Functor (C ×C E) (D ×C K)
  :=
  {|F0 p := (F (fst p), G (snd p))
  ; F1 X Y f := (fmap F (fst f), fmap G (snd f))
  |}.
Next Obligation.
  intros [f g] [f' g'] [Hf Hg]. split; cbn.
  - exact (@functor_fmap_proper _ _ F _ _ f f' Hf).
  - exact (@functor_fmap_proper _ _ G _ _ g g' Hg).
Qed.
Next Obligation. split; apply functor_id. Qed.
Next Obligation. split; apply functor_comp. Qed.

Infix "×F" := ProdF (at level 41) : cat_scope.

(** A functor preserves identities transported along native object equality. *)

(** 函子保持沿对象原生相等运输的恒等态射。 *)

Lemma fmap_eq_to_hom {C D : Cat} (F : Functor C D)
    {X Y : @Ob C} (p : X = Y)
  : fmap F (eq_to_hom p) ≈ eq_to_hom (f_equal F p).
Proof. destruct p. simpl. apply functor_id. Qed.

(** ** Opposite Functors

    Taking opposites reverses arrows in both categories. Double opposition is
    compared by explicit identity-on-objects-and-morphisms functors, without
    requiring equality of category records or their law proofs. *)

(** ** 反函子

    取反同时反转两侧范畴的箭头。双重取反通过在对象和态射上为恒等的显式函子比较，
    不要求范畴记录或定律证明原生相等。 *)

Program Definition OpF {C D : Cat} (F : Functor C D)
  : Functor (C ^op) (D ^op)
  :=
  {|F0 X := F X
  ; F1 X Y f := fmap F f
  |}.
Next Obligation.
  intros u v Huv. exact (@functor_fmap_proper C D F Y X u v Huv).
Qed.
Next Obligation. exact (@functor_id C D F X). Qed.
Next Obligation. exact (@functor_comp C D F Z Y X g f). Qed.

Notation "F '^opF'" := (OpF F) (at level 35) : cat_scope.

(** Read a functor between opposite categories in the original categories.
    This keeps the underlying maps, without comparing category records. *)

(** 将反范畴之间的函子读作原范畴之间的函子，保留底层映射，不比较范畴记录。 *)

Program Definition UnopF {C D : Cat} (F : Functor (C^op) (D^op))
  : Functor C D
  :=
  {|F0 X := F X
  ; F1 X Y f := fmap F f
  ; functor_fmap_proper X Y f g H :=
      @functor_fmap_proper (C^op) (D^op) F Y X f g H
  |}.
Next Obligation. exact (@functor_id (C^op) (D^op) F X). Qed.
Next Obligation. exact (@functor_comp (C^op) (D^op) F Z Y X g f). Qed.

Notation "F '^unopF'" := (UnopF F) (at level 35) : cat_scope.

(** The identity action from a category to its double opposite. *)

(** 从范畴到其双重反范畴的恒等作用。 *)

Program Definition ToDoubleOpF {C : Cat}
  : Functor C (C ^op ^op)
  :=
  {|F0 X := X
  ; F1 X Y f := f
  |}.
Next Obligation. intros f g Hfg. exact Hfg. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** The identity action from the double opposite back to the category. *)

(** 从双重反范畴返回原范畴的恒等作用。 *)

Program Definition FromDoubleOpF {C : Cat}
  : Functor (C ^op ^op) C
  :=
  {|F0 X := X
  ; F1 X Y f := f
  |}.
Next Obligation. intros f g Hfg. exact Hfg. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
