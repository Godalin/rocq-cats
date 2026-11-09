From Cats Require Import Cat.Core.



(** * Functor *)

(** * 函子 *)

(** A functor transports objects and arrows from [C] to [D], preserving
    the category operations. Its preservation laws compare parallel arrows
    in [D], without requiring native equality of functions or law witnesses.
    Respecting hom equality is part of every functor; reflecting it is the
    additional faithfulness property introduced below. *)

(** 函子将 [C] 的对象和箭头送入 [D]，并保持范畴运算。保持定律比较 [D] 中的
    平行箭头，不要求函数或定律见证的原生相等。每个函子都必须保持 Hom 相等；
    反映这种相等则是下文另行定义的忠实性。 *)

Record Functor (C D : Cat)
  :=
  (** [F0] maps objects. The [:>] coercion lets us write its value as [F X]. *)

  (** [F0] 映射对象。[:>] 强制转换使其值可直接记为 [F X]。 *)

  { F0 :> @Ob C → @Ob D
  (** [F1] maps [f : Hom X Y] to an arrow from [F X] to [F Y]. Below,
      [fmap F f] names this action. Its endpoints depend on [F0]. *)

  (** [F1] 将 [f : Hom X Y] 映为从 [F X] 到 [F Y] 的箭头，下文用
      [fmap F f] 表示这个作用。像箭头的端点由 [F0] 决定。 *)

  ; F1 {X Y : @Ob C} : Hom X Y → Hom (F0 X) (F0 Y)

  (** [functor_fmap_proper] sends equal source arrows to equal target
      arrows. The two categories use their own specified hom equalities;
      these need not be native equality or the same relation. *)

  (** [functor_fmap_proper] 将源范畴中相等的箭头送到目标范畴中相等的箭头。
      两侧使用各自指定的 Hom 相等，不必是原生相等，也不必是同一个关系。 *)

  ; functor_fmap_proper {X Y}
    :: Proper (@HomEq[X, Y] ==> @HomEq[F0 X, F0 Y]) F1

  (** [functor_id] states [fmap F (@id X) ≈ @id (F X)]. *)

  (** [functor_id] 给出 [fmap F (@id X) ≈ @id (F X)]。 *)

  ; functor_id {X}
    : F1 (@id X) ≈ @id (F0 X)

  (** [functor_comp] states [fmap F (f ∘ g) ≈ fmap F f ∘ fmap F g]. A path
      can be composed before or after applying the functor, with equal results. *)

  (** [functor_comp] 给出 [fmap F (f ∘ g) ≈ fmap F f ∘ fmap F g]：
      先复合再映射，与先映射再复合，得到相等的箭头。 *)

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

(** A fully faithful functor reflects invertibility. Fullness supplies an
    inverse preimage, and faithfulness reflects its two inverse equations. *)

(** 全忠实函子反映可逆性：满性提供逆的原像，忠实性反映两条互逆方程。 *)

Definition functor_reflects_iso {C D : Cat} (F : Functor C D)
    (HF : is_fully_faithful F) {X Y : @Ob C} (f : Hom X Y)
    (Hf : is_iso (fmap F f))
  : is_iso f.
Proof.
  destruct (fst HF Y X Hf.1) as [g Hg].
  exists g. split; apply (snd HF); rewrite functor_comp, Hg, functor_id;
    [exact (fst Hf.2) | exact (snd Hf.2)].
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

(** Taking opposites preserves chosen arrow preimages. *)

(** 取反保留选定的箭头原像。 *)

Definition functor_op_full {C D : Cat} {F : Functor C D}
    (HF : is_full F)
  : is_full (F^opF)
  := λ X Y f, HF Y X f.

(** Inverting the representative isomorphism gives essential surjectivity
    in the opposite category, with the same object representatives. *)

(** 反转代表同构给出反范畴中的本质满性，并保留原对象代表。 *)

Definition functor_op_essentially_surjective {C D : Cat}
    {F : Functor C D} (HF : is_essentially_surjective F)
  : is_essentially_surjective (F^opF).
Proof.
  intros Y. destruct (HF Y) as [X e].
  exists X, e.2.1, e.1. split;
    [exact (fst e.2.2) | exact (snd e.2.2)].
Defined.

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

(** The double-opposite inclusion is full, with the same arrow as preimage. *)

(** 双重反范畴嵌入是满的，箭头的原像就是它本身。 *)

Definition to_double_op_full {C : Cat}
  : is_full (@ToDoubleOpF C).
Proof. intros X Y f. exists f. reflexivity. Defined.

(** Every double-opposite object is represented by itself. *)

(** 每个双重反范畴对象以自身为代表。 *)

Definition to_double_op_essentially_surjective {C : Cat}
  : is_essentially_surjective (@ToDoubleOpF C).
Proof. intro X. exists X. exact (@iso_refl (C^op^op) X). Defined.

(** Removing double opposition is full with the identity preimage map. *)

(** 去除双重取反是满的，原像映射为恒等。 *)

Definition from_double_op_full {C : Cat}
  : is_full (@FromDoubleOpF C).
Proof. intros X Y f. exists f. reflexivity. Defined.

(** Removing double opposition is essentially surjective on objects. *)

(** 去除双重取反在对象上本质满。 *)

Definition from_double_op_essentially_surjective {C : Cat}
  : is_essentially_surjective (@FromDoubleOpF C).
Proof. intro X. exists X. exact (@iso_refl C X). Defined.
