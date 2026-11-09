From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift
  Instance.Set.Yoneda.

(** * Representations and Universal Elements

    The source category is arbitrary. All equalities and uniqueness laws use
    the specified hom/setoid equality; mediators remain transparent. *)

(** * 表示与泛元素

    源范畴任意，全部相等和唯一性使用指定 Hom 或广集相等，中介保持透明。 *)

Definition is_universal_element {C : Cat} (F : Functor C SetCat)
    {X : @Ob C} (u : F X)
  := ∀ Y (y : F Y), ∃ f : Hom X Y, is_unique (λ f, fmap F f u ≈S y) f.

Notation "u '⦂' 'Univ(' F ')'" := (is_universal_element F u)
  (at level 50, no associativity,
    format "u  ⦂  Univ( F )") : cat_scope.

Section UniversalElements.
Context {C : Cat} (F : Functor C SetCat).

(** A universal element detects equality of arrows through its functorial
    images. *)

(** 泛元素通过函子像检测箭头相等。 *)

Theorem universal_element_hom_ext {X Y : @Ob C} {u : F X}
    (Hu : u ⦂ Univ(F)) (f g : Hom X Y)
  : fmap F f u ≈S fmap F g u → f ≈ g.
Proof.
  intros H. destruct (Hu Y (fmap F g u)) as [h Hh].
  transitivity h.
  - apply (@that _ _ _ _ _ Hh). exact H.
  - symmetry. apply (@that _ _ _ _ _ Hh). reflexivity.
Qed.

(** Send a value to its unique representing arrow. *)

(** 将值送到其唯一表示箭头。 *)

Program Definition universal_element_inverse_resp {X : @Ob C} {u : F X}
    (Hu : u ⦂ Univ(F)) (Y : @Ob C)
  : F Y →r HomSet X Y
  :=
  {|func y := (Hu Y y).1
  |}.
Next Obligation.
  intros y z H. apply (@that _ _ _ _ _ (Hu Y z).2).
  transitivity y; [exact (@this _ _ _ _ _ (Hu Y y).2) | exact H].
Defined.

(** A universal element gives a natural representation by a hom functor. *)

(** 泛元素给出由 Hom 函子表示的自然表示。 *)

Definition universal_element_representation {X : @Ob C} {u : F X}
    (Hu : u ⦂ Univ(F))
  : X ⦂ Rep F.
Proof.
  exists (yoneda_func_inv u). intros Y.
  exists (universal_element_inverse_resp Hu Y). split.
  - intros f. symmetry. apply (@that _ _ _ _ _ (Hu Y (fmap F f u)).2). reflexivity.
  - intros y. exact (@this _ _ _ _ _ (Hu Y y).2).
Defined.

(** Two universal elements for one functor have isomorphic carrier objects. *)

(** 同一函子的两个泛元素具有同构的承载对象。 *)

Definition universal_element_iso {X Y : @Ob C} {u : F X} {v : F Y}
    (Hu : u ⦂ Univ(F)) (Hv : v ⦂ Univ(F))
  : X ≅[C] Y.
Proof.
  exists (Hu Y v).1, (Hv X u).1. split.
  - apply (universal_element_hom_ext Hu).
    transitivity (fmap F (Hv X u).1 (fmap F (Hu Y v).1 u)).
    + exact (functor_comp C SetCat F _ _ u).
    + transitivity (fmap F (Hv X u).1 v).
      * apply func_proper. exact (@this _ _ _ _ _ (Hu Y v).2).
      * transitivity u.
        -- exact (@this _ _ _ _ _ (Hv X u).2).
        -- symmetry. exact (functor_id C SetCat F u).
  - apply (universal_element_hom_ext Hv).
    transitivity (fmap F (Hu Y v).1 (fmap F (Hv X u).1 v)).
    + exact (functor_comp C SetCat F _ _ v).
    + transitivity (fmap F (Hu Y v).1 u).
      * apply func_proper. exact (@this _ _ _ _ _ (Hv X u).2).
      * transitivity v.
        -- exact (@this _ _ _ _ _ (Hu Y v).2).
        -- symmetry. exact (functor_id C SetCat F v).
Defined.

End UniversalElements.

Section Representations.
Context {C : Cat} {F : Functor C SetCat}.

(** The value of the representing transformation at the identity arrow. *)

(** 表示自然变换在恒等箭头处的值。 *)

Definition representation_generic {X : @Ob C} (R : X ⦂ Rep F)
  : F X
  := yoneda_func R.1.

(** Every representation component is the image of its generic element. *)

(** 表示的每个分量都是其泛元素的像。 *)

Theorem representation_at {X Y : @Ob C} (R : X ⦂ Rep F) (f : Hom X Y)
  : R.1 Y f ≈S fmap F f (representation_generic R).
Proof.
  symmetry. exact (yoneda_func_inv_func R.1 Y f).
Defined.

(** The generic element extracted from a representation is universal. *)

(** 从表示提取的泛元素满足泛性质。 *)

Definition representation_universal {X : @Ob C} (R : X ⦂ Rep F)
  : representation_generic R ⦂ Univ(F).
Proof.
  intros Y y. exists ((R.2 Y).1 y). refine {|this := _
                                           ; that := _
                                           |}.
  - transitivity (R.1 Y ((R.2 Y).1 y)).
    + symmetry. apply representation_at.
    + exact (snd (R.2 Y).2 y).
  - intros f Hf. transitivity ((R.2 Y).1 (R.1 Y f)).
    + symmetry. exact (fst (R.2 Y).2 f).
    + apply func_proper. transitivity (fmap F f (representation_generic R)).
      * apply representation_at.
      * exact Hf.
Defined.

(** An object represents a functor exactly when it carries a universal
    element. *)

(** 对象表示函子，当且仅当它承载该函子的泛元素。 *)

Theorem represents_iff_universal_element (X : @Ob C)
  : (X ⦂ Rep F) ↔ ∃ u : F X, u ⦂ Univ(F).
Proof.
  split.
  - intros R. exists (representation_generic R). apply representation_universal.
  - intros [u Hu]. exact (universal_element_representation F Hu).
Defined.

(** Recovering a representation from its generic element preserves its natural
    map. *)

(** 由泛元素恢复表示后保持原自然映射。 *)

Theorem representation_round_trip {X : @Ob C} (R : X ⦂ Rep F)
  : (universal_element_representation F (representation_universal R)).1 ≈N R.1.
Proof. intros Y f. symmetry. apply representation_at. Qed.

(** The representation constructed from a universal element retains that
    element. *)

(** 由泛元素构造的表示保留原泛元素。 *)

Theorem universal_element_generic {X : @Ob C} {u : F X}
    (Hu : u ⦂ Univ(F))
  : representation_generic (universal_element_representation F Hu) ≈S u.
Proof. exact (functor_id C SetCat F u). Defined.

(** Two representations of a functor induce an isomorphism of representing
    objects. *)

(** 同一函子的两个表示诱导表示对象之间的同构。 *)

Definition representation_iso {X Y : @Ob C}
    (R : X ⦂ Rep F) (S : Y ⦂ Rep F)
  : X ≅[C] Y
  := universal_element_iso F (representation_universal R) (representation_universal S).

(** The comparison is unique among maps preserving the universal element,
    rather than among all isomorphisms between the two objects. *)

(** 比较在保持泛元素的映射中唯一，不声称两个对象之间的所有同构都相同。 *)

Theorem representation_iso_universal {X Y : @Ob C}
    (R : X ⦂ Rep F) (S : Y ⦂ Rep F)
  : is_unique
      (λ f, fmap F f (representation_generic R) ≈S representation_generic S)
      (representation_iso R S).1.
Proof. exact (representation_universal R Y (representation_generic S)).2. Defined.

End Representations.

(** ** Contravariant Representations

    Use the covariant theory in C^op, with the explicit Hom comparison. No
    duplicate universal-property proof or equality of functors is needed. *)

(** ** 反变表示

    通过显式 Hom 比较使用反范畴上的协变理论，不重复证明泛性质，也不要求函子原
    生相等。 *)

Definition represents_op {C : Cat} (P : Functor (C^op) SetCat) (X : @Ob C)
  := Hom(-,X) ≅N P.

Notation "X '⦂' 'Repᵒᵖ' P" := (represents_op P X)
  (at level 50, no associativity, format "X  ⦂  Repᵒᵖ  P") : cat_scope.

(** Retain an object and its representation of a contravariant functor. *)

(** 保留反变函子的表示对象及表示数据。 *)

Definition is_representable_op {C : Cat} (P : Functor (C^op) SetCat)
  := ∃ X, X ⦂ Repᵒᵖ P.

Section PresheafRepresentations.
Context {C : Cat} {P : Functor (C^op) SetCat}.

(** Convert a contravariant representation to the covariant theory on the
    opposite category. *)

(** 将反变表示转为反范畴上的协变表示。 *)

Program Definition represents_op_covariant {X : @Ob C} (R : X ⦂ Repᵒᵖ P)
  : @represents (C^op) P X
  := (R.1 ∘Nv (hom_op_nat_iso X).1; _).
Next Obligation.
  exact (nt_comp_v_NatIso R.1 (hom_op_nat_iso X).1 R.2 (hom_op_nat_iso X).2).
Defined.

(** Extract the generic element from a contravariant representation. *)

(** 从反变表示提取泛元素。 *)

Definition representation_op_generic {X : @Ob C} (R : X ⦂ Repᵒᵖ P)
  : P X
  := representation_generic (represents_op_covariant R).

(** A contravariant representation component is substitution of its generic
    element. *)

(** 反变表示的分量就是其泛元素的替换。 *)

Theorem representation_op_at {X Y : @Ob C} (R : X ⦂ Repᵒᵖ P) (f : Hom Y X)
  : R.1 Y f ≈S fmap P f (representation_op_generic R).
Proof. exact (representation_at (represents_op_covariant R) f). Defined.

(** The generic element of a contravariant representation is universal in the
    opposite category. *)

(** 反变表示的泛元素在反范畴中满足泛性质。 *)

Definition representation_op_universal {X : @Ob C} (R : X ⦂ Repᵒᵖ P)
  : representation_op_generic R ⦂ Univ(P)
  := representation_universal (represents_op_covariant R).

(** A universal element in the opposite category supplies a contravariant
    representation. *)

(** 反范畴中的泛元素给出反变表示。 *)

Definition universal_element_representation_op {X : @Ob C} {u : P X}
    (Hu : u ⦂ Univ(P))
  : X ⦂ Repᵒᵖ P
  := transitivity (symmetry (hom_op_nat_iso X)) (universal_element_representation P Hu).

(** Contravariant representation is equivalent to a universal element in the
    opposite category. *)

(** 反变表示等价于反范畴中的泛元素。 *)

Theorem represents_op_iff_universal_element (X : @Ob C)
  : (X ⦂ Repᵒᵖ P) ↔ ∃ u : P X, u ⦂ Univ(P).
Proof.
  split.
  - intros R. exists (representation_op_generic R). apply representation_op_universal.
  - intros [u Hu]. exact (universal_element_representation_op Hu).
Defined.

(** The contravariant representation round trip preserves the natural map. *)

(** 反变表示的往返构造保持原自然映射。 *)

Theorem representation_op_round_trip {X : @Ob C} (R : X ⦂ Repᵒᵖ P)
  : (universal_element_representation_op (representation_op_universal R)).1
      ≈N R.1.
Proof. intros Y f. symmetry. apply representation_op_at. Qed.

(** The contravariant representation retains the universal element used to
    construct it. *)

(** 反变表示保留构造它所用的泛元素。 *)

Theorem universal_element_op_generic {X : @Ob C} {u : P X}
    (Hu : u ⦂ Univ(P))
  : representation_op_generic (universal_element_representation_op Hu) ≈S u.
Proof. exact (functor_id (C^op) SetCat P u). Defined.

(** Two contravariant representations have isomorphic representing objects. *)

(** 两个反变表示具有同构的表示对象。 *)

Definition representation_op_iso {X Y : @Ob C}
    (R : X ⦂ Repᵒᵖ P) (S : Y ⦂ Repᵒᵖ P)
  : X ≅[C] Y.
Proof.
  pose (I := representation_iso (represents_op_covariant R) (represents_op_covariant S)).
  exists I.2.1, I.1. split; [exact (fst I.2.2) | exact (snd I.2.2)].
Defined.

(** The comparison of contravariant representations is uniquely determined by
    their generic elements. *)

(** 反变表示间的比较由其泛元素唯一确定。 *)

Theorem representation_op_iso_universal {X Y : @Ob C}
    (R : X ⦂ Repᵒᵖ P) (S : Y ⦂ Repᵒᵖ P)
  : is_unique
      (λ f, fmap P f (representation_op_generic S) ≈S representation_op_generic R)
      (representation_op_iso R S).1.
Proof. exact (representation_op_universal S X (representation_op_generic R)).2. Defined.

End PresheafRepresentations.

(** ** Representations at a Common Ambient Size

    The representing category and the values need not have the same native
    hom universes. Lift only the hom functor, retaining the original equality
    inside its wrapper. No resizing or equality of native sizes is required. *)

(** ** 共同环境大小中的表示

    表示范畴与函子值不必具有相同的原生 Hom 宇宙。只提升 Hom 函子，在包装内
    保留原指定相等；不要求大小重设或原生宇宙相同。 *)

Definition represents_lifted@{u p +} {C : Cat}
    (F : Functor C SetCat@{u p _ _ _ _ _}) (X : @Ob C)
  : Type
  := (LiftF ∘F Hom(X,-)) ≅N F.

Notation "X '⦂' 'Rep↑' F" := (represents_lifted F X)
  (at level 50, no associativity, format "X  ⦂  Rep↑  F") : cat_scope.

Section LiftedRepresentations.
Universe u p.
Context {C : Cat} (F : Functor C SetCat@{u p _ _ _ _ _}).

(** Reuse presheaf Yoneda on the opposite category for the covariant
    lifted hom functor. Only its endpoints are repackaged. *)

(** 在反范畴上复用预层 Yoneda，得到协变提升 Hom 函子的构造，只重新包装端点。 *)

Program Definition LiftedYonedaN {X : @Ob C} (x : F X)
  : (LiftF ∘F Hom(X,-)) ⇒ F
  :=
  {|nt Y := presheaf_yoneda_inv_resp (C := C^op)
      (P := F ∘F FromDoubleOpF) x Y
  |}.
Next Obligation.
  exact (nt_naturality (presheaf_yoneda_inv_resp (C := C^op)
    (P := F ∘F FromDoubleOpF) x) f).
Defined.

(** A universal element represents the functor by lifted native hom-sets.
    Its inverse is the existing unique mediator, wrapped at the ambient size. *)

(** 泛元素通过提升后的原生 Hom 广集表示函子；其逆为已有唯一中介在环境大小
    中的包装。 *)

Program Definition universal_element_lifted_inverse_resp
    {X : @Ob C} {x : F X} (Hx : x ⦂ Univ(F)) (Y : @Ob C)
  : F Y →r LiftS@{_ _ u p} (HomSet X Y)
  :=
  {|func y := {|lower := (Hx Y y).1
               |}
  |}.
Next Obligation.
  intros y z E. refine {|lower := _
                       |}.
  exact (@func_proper _ _ (universal_element_inverse_resp F Hx Y) y z E).
Defined.

(** Assemble the lifted representation from its two respectful maps. *)

(** 由两个保相等映射组装提升表示。 *)

Definition universal_element_lifted_representation {X : @Ob C} {x : F X}
    (Hx : x ⦂ Univ(F))
  : X ⦂ Rep↑ F.
Proof.
  exists (LiftedYonedaN x). intros Y.
  exists (universal_element_lifted_inverse_resp Hx Y). split.
  - intros [f]. refine {|lower := _
                        |}.
    symmetry. apply (@that _ _ _ _ _ (Hx Y (fmap F f x)).2).
    reflexivity.
  - intros y. exact (@this _ _ _ _ _ (Hx Y y).2).
Defined.

(** Evaluate a lifted representation at the wrapped identity. *)

(** 在包装的恒等箭头处求值提升表示。 *)

Definition lifted_representation_generic {X : @Ob C} (R : X ⦂ Rep↑ F)
  : F X
  := R.1 X {|lower := id
            |}.

(** Naturality determines each component from its generic element. *)

(** 自然性从泛元素确定每个分量。 *)

Lemma lifted_representation_at {X Y : @Ob C} (R : X ⦂ Rep↑ F)
    (f : Hom X Y)
  : R.1 Y {|lower := f
            |} ≈S fmap F f (lifted_representation_generic R).
Proof.
  transitivity (R.1 Y {|lower := f ∘ id
                       |}).
  - apply func_proper. exact {|lower := symmetry (comp_id_r f)
                             |}.
  - exact (nt_naturality R.1 f {|lower := id
                               |}).
Defined.

(** The generic element is universal without identifying native hom sizes. *)

(** 泛元素满足泛性质，无需等同原生 Hom 大小。 *)

Definition lifted_representation_universal {X : @Ob C} (R : X ⦂ Rep↑ F)
  : lifted_representation_generic R ⦂ Univ(F).
Proof.
  intros Y y. exists (lower ((R.2 Y).1 y)).
  refine {|this := _
          ; that := _
          |}.
  - transitivity (R.1 Y ((R.2 Y).1 y)).
    + destruct ((R.2 Y).1 y) as [f].
      symmetry. apply lifted_representation_at.
    + exact (snd (R.2 Y).2 y).
  - intros f Hf.
    pose proof (fst (R.2 Y).2 {|lower := f
                              |}) as E.
    transitivity (lower ((R.2 Y).1 (R.1 Y {|lower := f
                                          |}))).
    + exact (symmetry (lower E)).
    + apply (λ E, lower (@func_proper _ _ ((R.2 Y).1) _ _ E)).
      transitivity (fmap F f (lifted_representation_generic R)).
      * apply lifted_representation_at.
      * exact Hf.
Defined.

(** Lifted representation and a universal element carry equivalent data. *)

(** 提升表示与泛元素携带等价的数据。 *)

Theorem represents_lifted_iff_universal_element (X : @Ob C)
  : (X ⦂ Rep↑ F) ↔ ∃ x : F X, x ⦂ Univ(F).
Proof.
  split.
  - intros R. exists (lifted_representation_generic R).
    apply lifted_representation_universal.
  - intros [x Hx]. exact (universal_element_lifted_representation Hx).
Defined.

End LiftedRepresentations.
