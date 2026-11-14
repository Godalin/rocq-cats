From Cats Require Export
  Cat.Induced.
(** * Inverting Fully Faithful Functors on Their Image Objects

    Fix a functor and Type-valued full-faithfulness data. Use its computational
    fullness witnesses to lift arrows between selected image objects,
    then construct an inverse to its induced functor. Object representatives
    outside that indexed image are neither needed nor selected. Category
    and equality sizes remain independent; no choice axiom is used. *)

(** * 在像对象上求完全忠实函子的逆

    固定函子及 Type 值完全忠实见证，使用可计算满性见证提升选定像对象之间的
    箭头，再构造诱导函子的逆。不需要也不选取索引像以外的对象代表。范畴及
    相等大小保持独立，不使用选择公理。 *)

Section FullyFaithful.
Context {C D : Cat} (F : Functor C D) (H : is_fully_faithful F).

(** Lift a target arrow through the chosen Type-valued fullness witness. *)

(** 沿选定 Type 值满性见证提升目标箭头。 *)

Definition fully_faithful_preimage {X Y : @Ob C}
    (f : Hom (F X) (F Y))
  : Hom X Y
  := (fst H X Y f).1.

(** The lifted arrow respects the target hom-setoid equality. *)

(** 提升的箭头保持目标 Hom 广集相等。 *)

Global Instance fully_faithful_preimage_proper {X Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@fully_faithful_preimage X Y).
Proof.
  intros f g Hfg. apply (snd H X Y).
  transitivity f; [exact (fst H X Y f).2 |].
  transitivity g; [exact Hfg | symmetry; exact (fst H X Y g).2].
Qed.

(** Lifting an image returns the source arrow in its specified equality. *)

(** 提升像箭头，在指定相等下返回源箭头。 *)

Lemma fully_faithful_preimage_image {X Y : @Ob C} (f : Hom X Y)
  : fully_faithful_preimage (fmap F f) ≈ f.
Proof.
  apply (snd H X Y). exact (fst H X Y (fmap F f)).2.
Qed.

(** Mapping a lifted arrow recovers the original target arrow. *)

(** 映射提升后的箭头，恢复原目标箭头。 *)

Lemma fully_faithful_image_preimage {X Y : @Ob C}
    (f : Hom (F X) (F Y))
  : fmap F (fully_faithful_preimage f) ≈ f.
Proof. exact (fst H X Y f).2. Qed.

(** The inverse keeps the value indices as objects and lifts only the
    arrows. *)

(** 逆函子保留值索引作为对象，只提升箭头。 *)

Program Definition FullyFaithfulInverseF
  : Functor (InducedCat (@Ob C) F) C
  :=
  {|F0 X := X
  ; F1 X Y f := fully_faithful_preimage f
  ; functor_fmap_proper X Y := fully_faithful_preimage_proper
  |}.
Next Obligation.
  change (fully_faithful_preimage (@id (F X)) ≈ @id X).
  apply (snd H X X). rewrite fully_faithful_image_preimage.
  symmetry. apply functor_id.
Defined.
Next Obligation.
  change (fully_faithful_preimage (f ∘ g) ≈
    fully_faithful_preimage f ∘ fully_faithful_preimage g).
  apply (snd H X Z). rewrite fully_faithful_image_preimage, functor_comp,
    !fully_faithful_image_preimage. reflexivity.
Defined.

(** Identity components compare lifting after the induced functor with
    identity. *)

(** 恒等分量将诱导函子后接提升与恒等函子比较。 *)

Program Definition FullyFaithfulUnitN
  : (FullyFaithfulInverseF ∘F InducedF F) ⇒ (@IdF C)
  := {|nt X := id|}.
Next Obligation.
  change (id ∘ fully_faithful_preimage (fmap F f) ≈ f ∘ id).
  rewrite comp_id_l, comp_id_r. apply fully_faithful_preimage_image.
Defined.

(** The source comparison has transparent identity inverse components. *)

(** 源比较具有透明的恒等逆分量。 *)

Definition FullyFaithfulUnitIso
  : (FullyFaithfulInverseF ∘F InducedF F) ≅N (@IdF C).
Proof.
  exists FullyFaithfulUnitN. intro X. exists id. split; apply comp_id_l.
Defined.

(** Identity components also compare the other composite on indexed image
    objects. *)

(** 恒等分量也比较索引像对象上的另一个复合。 *)

Program Definition FullyFaithfulCounitN
  : (InducedF F ∘F FullyFaithfulInverseF) ⇒ (@IdF (InducedCat (@Ob C) F))
  := {|nt X := id|}.
Next Obligation.
  change (id ∘ fmap F (fully_faithful_preimage f) ≈ f ∘ id).
  rewrite comp_id_l, comp_id_r. apply fully_faithful_image_preimage.
Defined.

(** The target comparison retains the same identity inverse data. *)

(** 目标比较保留同样的恒等逆数据。 *)

Definition FullyFaithfulCounitIso
  : (InducedF F ∘F FullyFaithfulInverseF) ≅N (@IdF (InducedCat (@Ob C) F)).
Proof.
  exists FullyFaithfulCounitN. intro X. exists id. split; apply comp_id_l.
Defined.
End FullyFaithful.
