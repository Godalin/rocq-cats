From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.
From Cats Require Import Instance.Set.Lift.

(** * Hom-Functors *)

(** * Hom 函子 *)

(** The hom-setoid family with its source fixed. *)

(** 固定源对象的 Hom 广集族。 *)

Definition ℎ1 {C : Cat} (X : Ob)
  := λ Y, HomSet X Y.
(** The hom-setoid family with its target fixed. *)

(** 固定目标对象的 Hom 广集族。 *)

Definition ℎ2 {C : Cat} (X : Ob)
  := λ Y, HomSet Y X.

(** Postcomposition gives the covariant hom functor with a fixed source. *)

(** 后合成给出固定源对象的协变 Hom 函子。 *)

Program Definition ℎ1F {C : Cat} (X : Ob)
  : Functor C SetCat
  :=
  {|F0 := ℎ1 X
  ; F1 Y Y' (f : Hom Y Y') := f _*
  |}.
Next Obligation. intros f f' Hf g. simpl. rewrite Hf. cato. Qed.
Next Obligation. intros f. exact (@comp_id_l C _ _ f). Qed.
Next Obligation. intros x. exact (@comp_assoc C _ _ _ _ f g x). Qed.

Notation "'Hom(' X  ',-)'" := (ℎ1F X).

(** Precomposition gives the contravariant hom functor with a fixed target. *)

(** 预合成给出固定目标对象的反变 Hom 函子。 *)

Program Definition ℎ2F {C : Cat} (X : Ob)
  : Functor (op C) SetCat
  :=
  {|F0 := ℎ2 X
  ; F1 Y Y' (f : (@Hom C) Y' Y) := f ^*
  |}.
Next Obligation. intros f f' Hf g. simpl. rewrite Hf. cato. Qed.
Next Obligation. intros f. exact (@comp_id_r C _ _ f). Qed.
Next Obligation. intros x. symmetry. exact (@comp_assoc C _ _ _ _ x g f). Qed.

Notation "'Hom(-,'  X ')'" := (ℎ2F X).

(** Covariant Hom in the opposite category is contravariant Hom in C. Compare
    the functors explicitly, without equating their law fields. *)

(** 反范畴上的协变 Hom 就是 C 上的反变 Hom；显式比较函子而不等同定律字段。 *)

Program Definition hom_op_nat_iso {C : Cat} (X : @Ob C)
  : @ℎ1F (C^op) X ≅N Hom(-,X)
  := ({|nt Y := id_resp
      |}; _).
Next Obligation. intros h. reflexivity. Defined.
Next Obligation. intros Y. exists id_resp. split; intros h; reflexivity. Defined.

(** Precomposition varies the source of the covariant Hom-functor
    contravariantly. Its components compare maps pointwise. *)

(** 预合成使协变 Hom 函子的源反变地变化，其分量逐点比较映射。 *)

Program Definition nt_comp_pre {C : Cat} {X Y : @Ob C} (f : Hom X Y)
  : Hom(Y,-) ⇒ Hom(X,-)
  :=
  {|nt Z := comp_r_resp (f := f) (Z := Z)
  |}.
Next Obligation. intros h. simpl. apply comp_assoc. Qed.

Notation "f ^*N" := (nt_comp_pre f) (at level 35) : cat_scope.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance nt_comp_pre_proper {C : Cat} {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==> NatEq) (@nt_comp_pre C X Y).
Proof. intros f g Hfg Z h. simpl. rewrite Hfg. reflexivity. Qed.

(** Compatibility with identities for [nt_comp_pre]. *)

(** [nt_comp_pre] 与恒等的相容性。 *)

Theorem nt_comp_pre_id {C : Cat} {X : @Ob C}
  : (@id X) ^*N ≈N idN.
Proof. intros Z h. simpl. apply comp_id_r. Qed.

(** Compatibility with composition for [nt_comp_pre]. *)

(** [nt_comp_pre] 与复合的相容性。 *)

Theorem nt_comp_pre_comp {C : Cat} {X Y Z : @Ob C}
    (g : Hom Y Z) (f : Hom X Y)
  : (g ∘ f) ^*N ≈N (f ^*N ∘Nv g ^*N).
Proof. intros W h. simpl. symmetry. apply comp_assoc. Qed.

(** Postcomposition varies the target of the contravariant Hom-functor
    covariantly. *)

(** 后合成使反变 Hom 函子的目标协变地变化。 *)

Program Definition nt_comp_post {C : Cat} {X Y : @Ob C} (f : Hom X Y)
  : Hom(-,X) ⇒ Hom(-,Y)
  :=
  {|nt Z := comp_l_resp (C := C) (f := f) (X := Z)
  |}.
Next Obligation. intros h. simpl. symmetry. apply comp_assoc. Qed.

Notation "f _*N" := (nt_comp_post f) (at level 35) : cat_scope.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance nt_comp_post_proper {C : Cat} {X Y : @Ob C}
  : Proper (@HomEq[X, Y] ==> NatEq) (@nt_comp_post C X Y).
Proof. intros f g Hfg Z h. simpl. rewrite Hfg. reflexivity. Qed.

(** Compatibility with identities for [nt_comp_post]. *)

(** [nt_comp_post] 与恒等的相容性。 *)

Theorem nt_comp_post_id {C : Cat} {X : @Ob C}
  : (@id X) _*N ≈N idN.
Proof. intros Z h. simpl. apply comp_id_l. Qed.

(** Compatibility with composition for [nt_comp_post]. *)

(** [nt_comp_post] 与复合的相容性。 *)

Theorem nt_comp_post_comp {C : Cat} {X Y Z : @Ob C}
    (g : Hom Y Z) (f : Hom X Y)
  : (g ∘ f) _*N ≈N (g _*N ∘Nv f _*N).
Proof. intros W h. simpl. apply comp_assoc. Qed.

(** Precompose and postcompose a hom-setoid element by the two given arrows. *)

(** 将 Hom 广集元素分别与给定的两条箭头预合成及后合成。 *)

Program Canonical bi_comp {C : Cat} {X' X Y Y' : @Ob C}
    (f : (@Hom op C) X X') (g : Hom Y Y')
  : HomSet X Y →r HomSet X' Y'
  :=
  {|func := λ h, g ∘ h ∘ f
  |}.
Next Obligation. intros h h' Hh. rewrite Hh. cato. Qed.

(** The two-variable hom functor, contravariant in source and covariant in
    target. *)

(** 源反变、目标协变的双变量 Hom 函子。 *)

Program Definition HomF {C : Cat}
  : Functor (op C ×C C) SetCat
  :=
  {|F0 X := (@HomSet C) (fst X) (snd X)
  ; F1 _ _ f := bi_comp (fst f) (snd f)
  |}.
Next Obligation. simpl. intros [f g] [f' g'] [Hf Hg].
  simpl. intros h. simpl.
  rewrite Hf, Hg. reflexivity.
Qed.
Next Obligation. simpl. intros h. simpl; carw. Qed.
Next Obligation. destruct f as [f1 f2], g as [g1 g2]. intros k. simpl. repeat cacr. Qed.

(** Hom on either side of a pair of functors. A common ambient set category
    raises carrier and equality universes independently. Functoriality is
    inherited from HomF and composition, rather than reproved here. *)

(** 一对函子两侧的 Hom。共同环境集合范畴独立提升载体和相等见证宇宙；函子性由
    [HomF] 和复合继承，不再重证。 *)

Definition LeftHomF@{u p +} {C D : Cat} (F : Functor C D)
  : Functor (C^op ×C D) SetCat@{u p _ _ _ _ _}
  := LiftF ∘F (HomF ∘F (F^opF ×F IdF)).

(** The hom functor on the right side of an adjunction correspondence. *)

(** 伴随对应右侧的 Hom 函子。 *)

Definition RightHomF@{u p +} {C D : Cat} (G : Functor D C)
  : Functor (C^op ×C D) SetCat@{u p _ _ _ _ _}
  := LiftF ∘F (HomF ∘F (IdF ×F G)).

(** * Morphism Maps of Functors

    Full faithfulness makes this specific map an isomorphism of setoids. *)

(** * 函子的态射映射

    全忠实性使此指定映射成为广集同构。 *)

Program Canonical fmap_resp {C D : Cat} (F : Functor C D) {X Y : @Ob C}
  : HomSet X Y →r HomSet (F X) (F Y)
  :=
  {|func := fmap F (X := X) (Y := Y)
  |}.

(** A functor is fully faithful exactly when its specific hom maps are
    invertible. *)

(** 函子全忠实，当且仅当其指定 Hom 映射可逆。 *)

Theorem functor_fully_faithful_iff_hom_iso {C D : Cat} (F : Functor C D)
  : is_fully_faithful F ↔
      ∀ X Y, @is_iso SetCat _ _ (fmap_resp F (X := X) (Y := Y)).
Proof. split.
  - intros HF X Y.
    pose (Hfull := fst HF). pose (Hfaith := snd HF).
    unshelve notypeclasses refine (({|func := _
                                    |}); _).
    + exact (λ g, (Hfull X Y g).1).
    + intros g h Hgh. apply (Hfaith X Y).
      transitivity g. exact (Hfull X Y g).2.
      transitivity h. exact Hgh. symmetry. exact (Hfull X Y h).2.
    + split.
      * intros f. apply (Hfaith X Y). exact (Hfull X Y (fmap F f)).2.
      * intros g. exact (Hfull X Y g).2.
  - intros Hiso. split.
    + intros X Y g. exists ((Hiso X Y).1 g).
      exact (snd ((Hiso X Y).2) g).
    + intros X Y f g Hfg. destruct (Hiso X Y) as [i [Hl Hr]].
      transitivity (i (fmap F f)). symmetry. exact (Hl f).
      transitivity (i (fmap F g)). apply func_proper. exact Hfg.
      exact (Hl g).
Defined.

(** Isomorphisms of source and target induce a native hom-setoid
    isomorphism. This is the action of the existing Hom bifunctor. *)

(** 源及目标的同构诱导原生 Hom 广集同构；这是已有 Hom 双函子的作用。 *)

Definition hom_iso {C : Cat} {X X' Y Y' : @Ob C}
    (i : X' ≅ X) (j : Y ≅ Y')
  : HomSet X Y ≅[SetCat] HomSet X' Y'.
Proof.
  refine (bi_comp i.1 j.1; _).
  apply (@functor_is_iso (C^op ×C C) SetCat HomF
    (X, Y) (X', Y') (i.1, j.1)).
  exists (i.2.1, j.2.1). split; split;
    [exact (snd i.2.2) | exact (fst j.2.2) |
     exact (fst i.2.2) | exact (snd j.2.2)].
Defined.
