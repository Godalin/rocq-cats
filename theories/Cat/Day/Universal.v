From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Natural
  Cat.Coend.Core
  Instance.Set.Core
  Instance.Set.Product.
From Cats Require Export
  Cat.Day.Map.

(** * Generators and the Universal Property of Day Convolution *)

(** * Day 卷积的生成元与泛性质 *)

(** Insert a fixed Hom weight while leaving the value pair variable.
    Separate weight and value indices also describe off-diagonal terms. *)

(** 插入固定 Hom 权重而保留值对可变；独立的权重和值指标也描述非对角项。 *)

Program Definition day_weight@{u p +} {C : Cat} (T : Functor (C ×C C) C)
    (F G : Functor C (SetCat@{u p _ _ _ _ _})) {Z : @Ob C}
    (p q : @Ob (C ×C C)) (h : Hom (T p) Z)
  : DayValuesF F G q →r DayKernel T F G Z (p, q)
  :=
  {|func xy := ({|lower := h|}, xy)
  |}.
Next Obligation.
  intros xy xy' H. split; [exact {|lower := reflexivity h|} | exact H].
Defined.

(** ** Weight Transport

    Fix the binary functor and its two inputs. The following equations
    expose the kernel action without expanding any selected coend. *)

(** ** 权重运输

    固定二元函子及其两个输入。以下方程暴露核作用，而不展开任何选定 coend。 *)

Section WeightLaws.
Universes u p.
Context {C : Cat} (T : Functor (C ×C C) C).
Context (F G : Functor C (SetCat@{u p _ _ _ _ _})).

(** A contravariant change precomposes the weight. *)

(** 逆变改变预合成权重。 *)

Lemma day_weight_pre {Z : @Ob C} {p p' : @Ob (C ×C C)}
    (q : @Ob (C ×C C)) (f : Hom p' p) (h : Hom (T p) Z)
  : fmap (DayKernel T F G Z) (X := (p,q)) (Y := (p',q)) (f,id)
      ∘ day_weight T F G p q h
    ≈ day_weight T F G p' q (h ∘ fmap T f).
Proof.
  intros xy. split; [reflexivity |].
  exact (@functor_id (C ×C C) SetCat (DayValuesF F G) q xy).
Defined.

(** A covariant change acts on the value pair and leaves the weight fixed. *)

(** 协变改变作用于值对并保持权重固定。 *)

Lemma day_weight_post {Z : @Ob C} (p : @Ob (C ×C C))
    {q q' : @Ob (C ×C C)} (f : Hom q q') (h : Hom (T p) Z)
  : fmap (DayKernel T F G Z) (X := (p,q)) (Y := (p,q')) (id,f)
      ∘ day_weight T F G p q h
    ≈ (day_weight T F G p q' h ∘r fmap (DayValuesF F G) f).
Proof.
  intros xy. split; [| reflexivity].
  refine {|lower := _|}. cbn.
  rewrite (@functor_id (C ×C C) C T p), comp_id_r. reflexivity.
Defined.

End WeightLaws.

(** ** Diagonal Injections

    Assume just the chosen convolutions of [F] and [G]. The injections
    express each representative as a value pair with a result arrow. *)

(** ** 对角注入

    只假定 [F] 与 [G] 的选定卷积；注入将每个代表表示为值对及结果箭头。 *)

Section Injections.
Universes u p.
Context {C : Cat} (T : Functor (C ×C C) C).
Context (F G : Functor C (SetCat@{u p _ _ _ _ _})) `{HD : !HasDay C T F G}.

(** A value pair and a weight give an element of the chosen convolution. *)

(** 值对和权重给出选定卷积的元素。 *)

Definition day_inject (p : @Ob (C ×C C)) {Z : @Ob C}
    (h : Hom (T p) Z)
  : (@Hom SetCat) (DayValuesF F G p) (DayF T F G Z)
  := ιcoend[DayKernel T F G Z] p ∘ day_weight T F G p p h.

(** Equivalent weights determine equivalent maps on value pairs. *)

(** 等价权重确定值对上的等价映射。 *)

Global Instance day_inject_proper (p : @Ob (C ×C C)) (Z : @Ob C)
  : Proper (@HomEq C (T p) Z ==>
      @HomEq SetCat (DayValuesF F G p) (DayF T F G Z))
      (@day_inject p Z).
Proof.
  intros h k H xy.
  apply (@func_proper _ _ (ιcoend[DayKernel T F G Z] p)).
  split; [exact {|lower := H|} | reflexivity].
Defined.

(** Changing the target postcomposes the representative's weight. *)

(** 改变目标会后合成代表的权重。 *)

Lemma day_inject_post (p : @Ob (C ×C C)) {Z Z' : @Ob C}
    (f : Hom Z Z') (h : Hom (T p) Z)
  : fmap (DayF T F G) f ∘ day_inject p h ≈ day_inject p (f ∘ h).
Proof.
  unfold day_inject.
  change (coend_map (DayPostN T f) ∘
    (ιcoend[DayKernel T F G Z] p ∘ day_weight T F G p p h) ≈
    ιcoend[DayKernel T F G Z'] p ∘ day_weight T F G p p (f ∘ h)).
  rewrite <- comp_assoc, (@coend_map_β (C ×C C) SetCat), comp_assoc.
  intros xy. reflexivity.
Defined.

(** Reindexing a value pair is exactly the coend's gluing equation. *)

(** 重索引值对恰好是 coend 的粘合方程。 *)

Lemma day_inject_gluing {p q : @Ob (C ×C C)}
    (f : Hom p q) {Z : @Ob C} (h : Hom (T q) Z)
  : day_inject p (h ∘ fmap T f) ≈
      day_inject q h ∘ fmap (DayValuesF F G) f.
Proof.
  unfold day_inject.
  rewrite <- (day_weight_pre T F G p f h), <- comp_assoc.
  rewrite (cowedge_comm ιcoend[DayKernel T F G Z] f), comp_assoc.
  rewrite (day_weight_post T F G q f h), <- comp_assoc. reflexivity.
Defined.

(** Outgoing maps are determined by their action on weighted value pairs. *)

(** 出射映射由其在加权值对上的作用确定。 *)

Lemma day_hom_ext {Z : @Ob C} {W : SetC}
    (f g : (@Hom SetCat) (DayF T F G Z) W)
    (H : ∀ p (h : Hom (T p) Z), f ∘ day_inject p h ≈ g ∘ day_inject p h)
  : f ≈ g.
Proof.
  apply (@coend_hom_ext (C ×C C) SetCat (DayKernel T F G Z)).
  intros p [[h] xy]. exact (H p h xy).
Defined.

(** The identity weight gives the generating pair at its tensor value. *)

(** 恒等权重在张量值处给出生成对。 *)

Program Definition DayGeneratorN
  : DayValuesF F G ⇒ (DayF T F G ∘F T)
  :=
  {|nt p := day_inject p id
  |}.
Next Obligation.
  change (day_inject Y id ∘ fmap (DayValuesF F G) f ≈
    fmap (DayF T F G) (fmap T f) ∘ day_inject X id).
  rewrite day_inject_post, comp_id_r.
  rewrite <- day_inject_gluing, comp_id_l. reflexivity.
Defined.

End Injections.

(** ** Extending a Natural Binary Operation

    Fix an output functor [H]. An operation from the external input product
    to [H ∘F T] evaluates a weighted pair by applying [H] to its weight.
    Naturality of the operation is precisely what makes this a cowedge. *)

(** ** 延拓自然的二元操作

    固定输出函子 [H]。从输入外积到 [H ∘F T] 的操作通过将 [H] 作用于权重来
    求值加权对。操作的自然性恰好保证这组成余楔。 *)

Section Extension.
Universes u p.
Context {C : Cat} (T : Functor (C ×C C) C).
Context {F G H : Functor C (SetCat@{u p _ _ _ _ _})}.
Context (β : DayValuesF F G ⇒ (H ∘F T)).

(** Evaluate the binary operation and then apply the weight. *)

(** 先求值二元操作，再作用权重。 *)

Program Definition day_extend_leg (Z : @Ob C) (p : @Ob (C ×C C))
  : DayKernel T F G Z (p,p) →r H Z
  :=
  {|func w := fmap H (lower (fst w)) (β p (snd w))
  |}.
Next Obligation.
  intros [h xy] [h' xy'] [Hh Hxy].
  transitivity (fmap H (lower h') (β p xy)).
  - exact (@functor_fmap_proper C SetCat H _ _ _ _ (lower Hh) (β p xy)).
  - apply func_proper. apply func_proper. exact Hxy.
Defined.

(** The operation's naturality identifies the two representatives of each
    reindexing, so evaluation descends through the selected coend. *)

(** 操作的自然性等同每次重索引的两个代表，因此求值经过选定 coend 下降。 *)

Program Definition DayExtendCowedge (Z : @Ob C)
  : Cowedge (DayKernel T F G Z) (H Z)
  := CowedgeOf (D := SetCat) (F := DayKernel T F G Z) (W := H Z)
      (day_extend_leg Z) _.
Next Obligation.
  intros [[h] xy].
  transitivity (day_extend_leg Z X
    (day_weight T F G X X (h ∘ fmap T f) xy)).
  - exact (@func_proper _ _ (day_extend_leg Z X) _ _
      (day_weight_pre T F G X f h xy)).
  - transitivity (day_extend_leg Z Y
      (day_weight T F G Y Y h (fmap (DayValuesF F G) f xy))).
    + change (fmap H (h ∘ fmap T f) (β X xy) ≈S
        fmap H h (β Y (fmap (DayValuesF F G) f xy))).
      transitivity (fmap H h (fmap H (fmap T f) (β X xy))).
      * exact (@functor_comp C SetCat H _ _ _ h (fmap T f) (β X xy)).
      * apply func_proper. symmetry. exact (nt_naturality β f xy).
    + symmetry. exact (@func_proper _ _ (day_extend_leg Z Y) _ _
        (day_weight_post T F G Y f h xy)).
Defined.

(** Selected coends assemble the extension as a natural transformation. *)

(** 选定 coend 将延拓组装为自然变换。 *)

Program Definition DayExtendN `{HD : !HasDay C T F G}
  : DayF T F G ⇒ H
  :=
  {|nt Z := coend⟨DayExtendCowedge Z⟩
  |}.
Next Obligation.
  change (coend⟨DayExtendCowedge Y⟩ ∘ coend_map (DayPostN T f) ≈
    fmap H f ∘ coend⟨DayExtendCowedge X⟩).
  apply (@coend_hom_ext (C ×C C) SetCat (DayKernel T F G X) _ (H Y)).
  intros p.
  change ((coend⟨DayExtendCowedge Y⟩ ∘ coend_map (DayPostN T f))
      ∘ ιcoend[DayKernel T F G X] p ≈
    (fmap H f ∘ coend⟨DayExtendCowedge X⟩)
      ∘ ιcoend[DayKernel T F G X] p).
  rewrite !comp_assoc, (@coend_map_β (C ×C C) SetCat), <- comp_assoc.
  pose proof (@coend_β (C ×C C) SetCat _ _ _ (DayExtendCowedge Y) p) as HY.
  change (coend⟨DayExtendCowedge Y⟩ ∘ ιcoend[DayKernel T F G Y] p
    ≈ day_extend_leg Y p) in HY.
  pose proof (@coend_β (C ×C C) SetCat _ _ _ (DayExtendCowedge X) p) as HX.
  change (coend⟨DayExtendCowedge X⟩ ∘ ιcoend[DayKernel T F G X] p
    ≈ day_extend_leg X p) in HX.
  rewrite HY, HX.
  intros [[h] xy]. exact (@functor_comp C SetCat H _ _ _ f h (β p xy)).
Defined.

End Extension.

(** ** The Natural Universal Correspondence

    Fix the pointwise coends and an output functor. Restriction to identity
    weights and extension along arbitrary weights are inverse in the
    specified natural-transformation equality, without function equality. *)

(** ** 自然的泛对应

    固定逐点 coend 和输出函子。限制到恒等权重与沿任意权重延拓在指定自然变换
    相等下互逆，不要求函数原生相等。 *)

Section UniversalCorrespondence.
Universes u p.
Context {C : Cat} (T : Functor (C ×C C) C).
Context {F G H : Functor C (SetCat@{u p _ _ _ _ _})}.
Context `{HD : !HasDay C T F G}.

(** Restrict an outgoing natural transformation to the generating pairs. *)

(** 将出射自然变换限制到生成对。 *)

Definition DayRestrictN (α : DayF T F G ⇒ H)
  : DayValuesF F G ⇒ (H ∘F T)
  := (α ∘Nr T) ∘Nv DayGeneratorN T F G.

(** An extension evaluates every weighted generator as prescribed. *)

(** 延拓按指定方式求值每个加权生成元。 *)

Lemma day_extend_β (β : DayValuesF F G ⇒ (H ∘F T))
    {Z : @Ob C} (q : @Ob (C ×C C)) (h : Hom (T q) Z)
  : DayExtendN T β Z ∘ day_inject T F G q h ≈ fmap H h ∘ β q.
Proof.
  change (coend⟨DayExtendCowedge T β Z⟩ ∘
    (ιcoend[DayKernel T F G Z] q ∘ day_weight T F G q q h) ≈
    fmap H h ∘ β q).
  rewrite <- comp_assoc.
  pose proof (@coend_β (C ×C C) SetCat _ _ _
    (DayExtendCowedge T β Z) q) as Hβ.
  change (coend⟨DayExtendCowedge T β Z⟩ ∘ ιcoend[DayKernel T F G Z] q
    ≈ day_extend_leg T β Z q) in Hβ.
  rewrite Hβ.
  intros xy. reflexivity.
Defined.

(** Restriction preserves the equality of natural transformations. *)

(** 限制保持自然变换的相等。 *)

Global Instance day_restrict_proper
  : Proper (NatEq ==> NatEq) DayRestrictN.
Proof.
  intros α γ K q xy. exact (K (T q) (day_inject T F G q id xy)).
Defined.

(** Extension preserves the equality of natural binary operations. *)

(** 延拓保持自然二元操作的相等。 *)

Global Instance day_extend_proper
  : Proper (NatEq ==> NatEq)
      (λ β : DayValuesF F G ⇒ (H ∘F T), DayExtendN T β).
Proof.
  intros β γ K Z.
  apply (@coend_desc_proper (C ×C C) SetCat).
  intros q [[h] xy].
  exact (@func_proper _ _ (fmap H h) _ _ (K q xy)).
Defined.

(** Extending and then restricting recovers the input binary operation. *)

(** 先延拓再限制恢复输入二元操作。 *)

Lemma day_restrict_extend (β : DayValuesF F G ⇒ (H ∘F T))
  : DayRestrictN (DayExtendN T β) ≈N β.
Proof.
  intros q.
  change (DayExtendN T β (T q) ∘ day_inject T F G q id ≈ β q).
  rewrite day_extend_β. intros xy.
  exact (@functor_id C SetCat H (T q) (β q xy)).
Defined.

(** Every outgoing transformation is recovered from its generating pairs. *)

(** 每个出射自然变换都从其生成对处的值恢复。 *)

Lemma day_extend_restrict (α : DayF T F G ⇒ H)
  : DayExtendN T (DayRestrictN α) ≈N α.
Proof.
  intros Z. apply (day_hom_ext T F G). intros q h.
  rewrite day_extend_β.
  change (fmap H h ∘ (α (T q) ∘ day_inject T F G q id) ≈
    α Z ∘ day_inject T F G q h).
  transitivity ((α Z ∘ fmap (DayF T F G) h) ∘ day_inject T F G q id).
  - rewrite (nt_naturality α h), comp_assoc. reflexivity.
  - rewrite comp_assoc, day_inject_post, comp_id_r. reflexivity.
Defined.

(** A prescribed restriction determines the extension uniquely. *)

(** 指定限制唯一确定延拓。 *)

Lemma day_extend_unique (β : DayValuesF F G ⇒ (H ∘F T))
    (α : DayF T F G ⇒ H) (K : DayRestrictN α ≈N β)
  : α ≈N DayExtendN T β.
Proof.
  transitivity (DayExtendN T (DayRestrictN α)).
  - symmetry. apply day_extend_restrict.
  - apply day_extend_proper. exact K.
Defined.

End UniversalCorrespondence.
