From Cats Require Export
  Cat.Equivalence.Core.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat
  Cat.Adjunction.

(** * Adjunctions from Specified Equivalences

    Full faithfulness and a chosen right quasi-inverse suffice. The hom
    correspondence is constructed from actual full preimages; no triangle
    equation between the initially supplied isomorphisms is required. *)

(** * 由指定等价构造伴随

    全忠实性及选定右拟逆已足够；Hom 对应由实际的满性原像构造，不要求最初
    给定的两个同构之间满足三角方程。 *)

Local Open Scope cat_scope.
Local Open Scope hom_scope.

Section FullyFaithfulAdjunction.
Context {C D : Cat} (F : Functor C D) (G : Functor D C)
    (HF : is_fully_faithful F) (v : (F ∘F G) ≅N IdF).

(** Lift an arrow after composing with the inverse target component. *)

(** 与目标分量的逆复合后提升箭头。 *)

Definition ff_adjunct {X : @Ob C} {Y : @Ob D} (f : Hom (F X) Y)
  : Hom X (G Y)
  := (fst HF X (G Y) ((v.2 Y).1 ∘ f)).1.

(** The lifted arrow has the specified image under the fully faithful
    functor. This equation controls all hom correspondence laws. *)

(** 提升箭头在全忠实函子下具有指定的像；此方程控制全部 Hom 对应定律。 *)

Lemma ff_adjunct_image {X : @Ob C} {Y : @Ob D} (f : Hom (F X) Y)
  : fmap F (ff_adjunct f) ≈ (v.2 Y).1 ∘ f.
Proof. exact (fst HF X (G Y) ((v.2 Y).1 ∘ f)).2. Qed.

(** The forward hom map respects designated hom equality. *)

(** 正向 Hom 映射保持指定 Hom 相等。 *)

Program Definition ff_adjunct_resp (X : @Ob C) (Y : @Ob D)
  : HomSet (F X) Y →r HomSet X (G Y)
  :=
  {|func := ff_adjunct
  |}.
Next Obligation.
  intros f g H. apply (snd HF).
  rewrite !ff_adjunct_image, H. reflexivity.
Defined.

(** The inverse hom map applies the functor and the supplied component. *)

(** 逆向 Hom 映射先应用函子，再应用给定分量。 *)

Program Definition ff_unadjunct_resp (X : @Ob C) (Y : @Ob D)
  : HomSet X (G Y) →r HomSet (F X) Y
  :=
  {|func g := v.1 Y ∘ fmap F g
  |}.
Next Obligation.
  intros f g H. rewrite H. reflexivity.
Defined.

(** The inverse laws and naturality build an adjunction. Only the target
    natural isomorphism is used once full faithfulness is supplied. *)

(** 互逆律及自然性组成伴随；给出全忠实性后，仅使用目标侧的自然同构。 *)

Definition FullyFaithfulAdjunction
  : F ⊣ G.
Proof.
  refine (AdjunctionFromHom F G ff_adjunct_resp ff_unadjunct_resp
    _ _ _ _).
  - intros X Y f.
    change (v.1 Y ∘ fmap F (ff_adjunct f) ≈ f).
    rewrite ff_adjunct_image, <- comp_assoc,
      (snd (v.2 Y).2), comp_id_l. reflexivity.
  - intros X Y g. apply (snd HF).
    change (fmap F (ff_adjunct (v.1 Y ∘ fmap F g)) ≈ fmap F g).
    rewrite ff_adjunct_image, <- comp_assoc,
      (fst (v.2 Y).2), comp_id_l. reflexivity.
  - intros X X' Y f h. apply (snd HF).
    change (fmap F (ff_adjunct (f ∘ fmap F h)) ≈
      fmap F (ff_adjunct f ∘ h)).
    rewrite functor_comp, !ff_adjunct_image, comp_assoc. reflexivity.
  - intros X Y Y' k f. apply (snd HF).
    change (fmap F (ff_adjunct (k ∘ f)) ≈
      fmap F (fmap G k ∘ ff_adjunct f)).
    rewrite functor_comp, !ff_adjunct_image, <- !comp_assoc.
    apply comp_proper; [| reflexivity].
    exact (nt_naturality (NatIso_inv v.1 v.2) k).
Defined.

End FullyFaithfulAdjunction.

(** Either direction of a quasi-inverse pair is an adjoint, using the
    full-faithfulness theorem rather than extra coherence assumptions. *)

(** 拟逆对的两个方向都可作为伴随，使用全忠实性定理而非额外相干假设。 *)

Definition QuasiInverseAdjunction {C D : Cat}
    (F : Functor C D) (G : Functor D C)
    (u : (G ∘F F) ≅N IdF) (v : (F ∘F G) ≅N IdF)
  : F ⊣ G
  := FullyFaithfulAdjunction F G (quasi_inverse_fully_faithful F G u v) v.

(** The forward functor of a specified category equivalence is left adjoint
    to its specified inverse. *)

(** 指定范畴等价的正向函子左伴随于指定逆函子。 *)

Definition EquivalenceAdjunction {C D : Cat} (e : C ≃C D)
  : e.1 ⊣ e.2.1
  := QuasiInverseAdjunction e.1 e.2.1 (fst e.2.2) (snd e.2.2).

(** Swapping the same data gives the opposite adjunction direction. *)

(** 交换同一份数据给出反向伴随。 *)

Definition EquivalenceInverseAdjunction {C D : Cat} (e : C ≃C D)
  : e.2.1 ⊣ e.1
  := QuasiInverseAdjunction e.2.1 e.1 (snd e.2.2) (fst e.2.2).
