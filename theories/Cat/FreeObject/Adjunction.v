From Cats Require Export
  Cat.FreeObject.Core
  Cat.Adjunction.
From Cats Require Import
  Cat.Monad.Adjunction.

(** * Free Objects Produce Adjunctions

    Initiality determines the action on arrows. Functoriality and the hom
    correspondence follow from unique factorization, so no additional
    naturality or functor action is chosen. *)

(** * 自由对象产生伴随

    始性确定态射作用；函子性及 Hom 对应均由唯一分解导出，不再另外选取自然性
    或函子作用。 *)

Section FreeAdjunction.
Context {C D : Cat} (U : Functor D C) `{HF : !HasFreeObjects U}.

(** Map an arrow by extending the target unit after that arrow. *)

(** 将箭头映为该箭头与目标单位复合后的唯一延拓。 *)

Program Definition FreeFunctor
  : Functor C D
  :=
  {|F0 := FreeOb U
  ; F1 X Y f := free_object_extend U (free_unit U Y ∘ f)
  |}.
Next Obligation.
  intros f g E. apply free_object_extend_proper.
  rewrite E. reflexivity.
Defined.
Next Obligation.
  symmetry. apply free_object_extend_unique.
  rewrite functor_id, comp_id_l, comp_id_r. reflexivity.
Defined.
Next Obligation.
  symmetry. apply free_object_extend_unique.
  rewrite functor_comp, comp_assoc, (free_object_extend_β U).
  rewrite <- comp_assoc, (free_object_extend_β U), comp_assoc. reflexivity.
Defined.

(** The defining factorization is naturality of the unit. *)

(** 定义所用分解方程正是单位自然性。 *)

Lemma free_functor_unit {X Y : @Ob C} (f : Hom X Y)
  : fmap U (fmap FreeFunctor f) ∘ free_unit U X ≈ free_unit U Y ∘ f.
Proof. apply free_object_extend_β. Qed.

(** The selected units form a natural transformation. *)

(** 选定单位组成自然变换。 *)

Program Definition FreeUnitN
  : IdF ⇒ U ∘F FreeFunctor
  :=
  {|nt := free_unit U
  |}.
Next Obligation. symmetry. apply free_functor_unit. Defined.

(** Factorization gives the forward hom map. *)

(** 分解给出正向 Hom 映射。 *)

Program Definition free_adjunct_resp (X : @Ob C) (A : @Ob D)
  : HomSet (FreeFunctor X) A →r HomSet X (U A)
  :=
  {|func g := fmap U g ∘ free_unit U X
  |}.
Next Obligation.
  intros f g E. rewrite E. reflexivity.
Defined.

(** Unique extension gives its inverse hom map. *)

(** 唯一延拓给出逆向 Hom 映射。 *)

Program Definition free_unadjunct_resp (X : @Ob C) (A : @Ob D)
  : HomSet X (U A) →r HomSet (FreeFunctor X) A
  :=
  {|func := free_object_extend U
  ; func_proper := free_object_extend_proper U
  |}.

(** Native hom maps and their inverse laws assemble the existing adjunction
    interface. Forward naturality suffices; inverse naturality is derived. *)

(** 原生 Hom 映射及互逆定律组装已有伴随接口；只需正向自然性，逆向自然性由此
    导出。 *)

Definition FreeAdjunction
  : FreeFunctor ⊣ U.
Proof.
  refine (AdjunctionFromHom FreeFunctor U
    free_adjunct_resp free_unadjunct_resp _ _ _ _).
  - intros X A g. apply free_object_extend_η.
  - intros X A f. apply free_object_extend_β.
  - intros X X' A g f.
    change (fmap U (g ∘ fmap FreeFunctor f) ∘ free_unit U X' ≈
      (fmap U g ∘ free_unit U X) ∘ f).
    rewrite functor_comp, comp_assoc, free_functor_unit, comp_assoc.
    reflexivity.
  - intros X A B k g. cbn.
    rewrite functor_comp, comp_assoc. reflexivity.
Defined.

(** The adjunction construction retains the selected unit up to hom equality. *)

(** 伴随构造按 Hom 相等保留选定单位。 *)

Lemma free_adjunction_unit (X : @Ob C)
  : adjunction_unit FreeAdjunction X ≈ free_unit U X.
Proof.
  change (fmap U id ∘ free_unit U X ≈ free_unit U X).
  rewrite functor_id, comp_id_l. reflexivity.
Qed.

(** Its counit is the extension of the identity at each [U]-image. *)

(** 其余单位是各 [U] 的像处恒等箭头的延拓。 *)

Lemma free_adjunction_counit (A : @Ob D)
  : adjunction_counit FreeAdjunction A ≈ free_object_extend U (@id (U A)).
Proof. reflexivity. Qed.

(** The free/forgetful monad reuses the general adjunction-to-monad theorem. *)

(** 自由／忘却 Monad 复用一般的伴随到 Monad 定理。 *)

Definition FreeMonad
  : Monad C
  := AdjunctionMonad FreeAdjunction.

End FreeAdjunction.

(** Every adjunction supplies chosen initial structured arrows through the
    universal property of its unit. The comparison stores actual mediators. *)

(** 每个伴随通过单位的泛性质给出选定始结构箭头，比较保留实际中介数据。 *)

Definition AdjunctionFreeObjects {C D : Cat}
    {F : Functor C D} {U : Functor D C} (A : F ⊣ U)
  : HasFreeObjects U.
Proof.
  refine (FreeObjectsFromUniversal U F (adjunction_unit A) _).
  intros X B f. exists (unadjunct A f). exact (adjunction_unit_universal A f).
Defined.

(** Having chosen free objects is equivalent to having a chosen left adjoint.
    Both sides carry data; neither uses Prop-only existence or choice. *)

(** 具有选定自由对象等价于具有选定左伴随；两侧均携带数据，不使用仅有 Prop 的
    存在性或选择公理。 *)

Theorem free_objects_iff_left_adjoint {C D : Cat} (U : Functor D C)
  : HasFreeObjects U ↔ ∃ F : Functor C D, F ⊣ U.
Proof.
  split.
  - intros H. exists (@FreeFunctor C D U H). exact (@FreeAdjunction C D U H).
  - intros [F A]. exact (AdjunctionFreeObjects A).
Defined.

(** Two selected families have unit-compatible isomorphisms pointwise. *)

(** 两组选定自由对象逐点具有与单位相容的同构。 *)

Definition free_object_choice_iso {C D : Cat} (U : Functor D C)
    (K L : HasFreeObjects U) (X : @Ob C)
  : ∃ i : @FreeOb C D U K X ≅[D] @FreeOb C D U L X,
      fmap U i.1 ∘ @free_unit C D U K X ≈ @free_unit C D U L X
  := universal_arrow_iso U (@free_universal C D U K X)
      (@free_universal C D U L X).

(** Uniqueness makes those pointwise comparisons natural. *)

(** 唯一性使逐点比较满足自然性。 *)

Program Definition FreeFunctorChoiceN {C D : Cat} (U : Functor D C)
    (K L : HasFreeObjects U)
  : @FreeFunctor C D U K ⇒ @FreeFunctor C D U L
  :=
  {|nt X := (free_object_choice_iso U K L X).1.1
  |}.
Next Obligation.
  apply (universal_arrow_hom_unique U (@free_universal C D U K X)).
  rewrite !functor_comp, !comp_assoc.
  rewrite (@free_functor_unit C D U K X Y f),
    (free_object_choice_iso U K L X).2.
  rewrite <- comp_assoc, (free_object_choice_iso U K L Y).2.
  symmetry. apply free_functor_unit.
Defined.

(** All choices of free objects yield naturally isomorphic left adjoints;
    this also compares the free-object/adjunction round trip. *)

(** 所有自由对象选取都给出自然同构的左伴随；这也比较自由对象／伴随的往返。 *)

Definition free_functor_choice_iso {C D : Cat} (U : Functor D C)
    (K L : HasFreeObjects U)
  : @FreeFunctor C D U K ≅N @FreeFunctor C D U L
  := (FreeFunctorChoiceN U K L;
      λ X, (free_object_choice_iso U K L X).1.2).

(** Recovering chosen initial objects from an adjunction and rebuilding its
    left adjoint preserves the original arrow action up to hom equality. *)

(** 从伴随恢复选定始对象再重建左伴随，按 Hom 相等保持原态射作用。 *)

Program Definition AdjunctionFreeRoundtripN {C D : Cat}
    {F : Functor C D} {U : Functor D C} (A : F ⊣ U)
  : @FreeFunctor C D U (AdjunctionFreeObjects A) ⇒ F
  :=
  {|nt X := id
  |}.
Next Obligation.
  rewrite comp_id_l, comp_id_r.
  change (@free_object_extend C D U (AdjunctionFreeObjects A) X (F Y)
    (adjunction_unit A Y ∘ f) ≈ fmap F f).
  symmetry. apply (@free_object_extend_unique C D U
    (AdjunctionFreeObjects A) X (F Y)).
  change (fmap U (fmap F f) ∘ adjunction_unit A X ≈
    adjunction_unit A Y ∘ f).
  symmetry. exact (nt_naturality (adjunction_unit A) f).
Defined.

(** The rebuilt left adjoint is naturally isomorphic to the original one.
    Equality of functor or adjunction proof fields is not required. *)

(** 重建左伴随与原左伴随自然同构，不要求函子或伴随证明字段相等。 *)

Definition adjunction_free_roundtrip_iso {C D : Cat}
    {F : Functor C D} {U : Functor D C} (A : F ⊣ U)
  : @FreeFunctor C D U (AdjunctionFreeObjects A) ≅N F.
Proof.
  exists (AdjunctionFreeRoundtripN A). intros X.
  exists id. split; apply comp_id_l.
Defined.

(** Compose free-object structures through the already proved composition
    of adjunctions, rather than repeating its universal-property proof. *)

(** 通过已有伴随复合定理复合自由对象结构，不重复泛性质证明。 *)

Definition CompositeFreeObjects {C D E : Cat}
    (U : Functor D C) (V : Functor E D)
    `{HU : !HasFreeObjects U} `{HV : !HasFreeObjects V}
  : HasFreeObjects (U ∘F V)
  := AdjunctionFreeObjects (CompAdjunction (FreeAdjunction V)
      (FreeAdjunction U)).

(** Initial structured arrows in the opposite categories construct a right
    adjoint. This is the left-adjoint theorem applied to opposites, followed
    by reading its hom correspondence in the original categories. *)

(** 反范畴中的始结构箭头构造右伴随；这是左伴随定理应用于反范畴，再将其 Hom
    对应读回原范畴。 *)

Definition CofreeAdjunction {C D : Cat} (U : Functor D C)
    `{HF : !HasFreeObjects (U^opF)}
  : U ⊣ (@FreeFunctor (C^op) (D^op) (U^opF) HF)^unopF.
Proof.
  pose (A := OpAdjunction (@FreeAdjunction (C^op) (D^op) (U^opF) HF)).
  refine (AdjunctionFromHom U
    ((@FreeFunctor (C^op) (D^op) (U^opF) HF)^unopF)
    (λ X Y, adjunct_resp A (X := X) (Y := Y))
    (λ X Y, unadjunct_resp A (X := X) (Y := Y)) _ _ _ _).
  - intros X Y f. exact (adjunction_β A f).
  - intros X Y g. exact (adjunction_η A g).
  - intros X X' Y f h. exact (adjunct_comp_r A f h).
  - intros X Y Y' k f. exact (adjunct_comp_l A k f).
Defined.

(** Chosen cofree objects mean chosen free objects for the opposite functor;
    their existence is constructively equivalent to a chosen right adjoint. *)

(** 选定余自由对象即反函子的选定自由对象；其存在构造性等价于选定右伴随。 *)

Theorem free_objects_op_iff_right_adjoint {C D : Cat} (U : Functor D C)
  : HasFreeObjects (U^opF) ↔ ∃ R : Functor C D, U ⊣ R.
Proof.
  split.
  - intros H. exists ((@FreeFunctor (C^op) (D^op) (U^opF) H)^unopF).
    exact (@CofreeAdjunction C D U H).
  - intros [R A]. exact (AdjunctionFreeObjects (OpAdjunction A)).
Defined.
