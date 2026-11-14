From Cats Require Export
  Cat.Computational.Arrow.StaticRepresentation
  Instance.Set.StaticInterpret.
From Cats Require Import
  Cat.Functor.FullyFaithful
  Cat.Computational.Arrow.Static
  Cat.Induced
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Exponential
  Instance.Set.Hom
  Cat.Exponential.Laws
  Cat.CatCat.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Exponential.Core.
Local Open Scope computation_scope.
(** * Reconstructing the Value-Indexed Computation Category

    Work in the existing closed setoid model at its common carrier/equality
    bound. The original computation-object size remains independent. Static
    representation is equivalent to full faithfulness of the interpreter;
    under that condition construct an equivalence with the computation
    category indexed by value objects. No representatives for other ambient
    objects are selected. *)

(** * 重建值索引计算范畴

    使用已有闭广集模型的共同载体／相等界，原计算对象大小仍独立。静态表示
    等价于解释函子的完全忠实性；在此条件下构造与值对象索引计算范畴的等价。
    不为环境中其他对象选取代表。 *)

Section Representation.
Universe u.
Let C
  : Cat
  := SetCat@{u u _ _ _ _ _}.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasExponential.
Context (K : Cat)
    (A : Arrow C K
      (@CartesianMonoidal C SetCat_HasTerminal SetCat_HasProduct)).

(** Compose singleton evaluation with the supplied static evaluation
    isomorphism. *)

(** 将单元素参数求值与给定静态求值同构复合。 *)

Definition static_interpret_hom_iso (H : is_static_arrow A) (X Y : @Ob C)
  : @HomSet (StaticCat (ArrowA K A)) X Y ≅[SetCat] HomSet (A X) (A Y)
  := @iso_trans SetCat _ _ _ (exponential_unit_iso (HomSet (A 1) (A (Y ^ X)%ob)))
      (arrow_static_eval_resp A X Y; H X Y).

(** Static representation implies full faithfulness by the existing Hom-
    isomorphism criterion. *)

(** 由已有 Hom 同构条件，静态表示蕴含完全忠实性。 *)

Definition static_interpret_fully_faithful (H : is_static_arrow A)
  : is_fully_faithful (StaticInterpretF K A).
Proof.
  apply (snd (functor_fully_faithful_iff_hom_iso (StaticInterpretF K A))).
  intros X Y. exact (static_interpret_hom_iso H X Y).2.
Defined.

(** Remove the same singleton-evaluation isomorphism to recover staticness
    from full faithfulness. *)

(** 移去同一个单元素求值同构，从完全忠实性恢复静态性。 *)

Definition static_interpret_static_of_fully_faithful
    (H : is_fully_faithful (StaticInterpretF K A))
  : is_static_arrow A.
Proof.
  intros X Y.
  exact (@iso_trans SetCat _ _ _
    (@iso_symm SetCat _ _ (exponential_unit_iso (HomSet (A 1) (A (Y ^ X)%ob))))
    (fmap_resp (StaticInterpretF K A);
      fst (functor_fully_faithful_iff_hom_iso (StaticInterpretF K A)) H X Y)).2.
Defined.

(** These are equivalent conditions for this particular static
    interpretation functor. *)

(** 对这个指定静态解释函子，两者是等价条件。 *)

Definition static_interpret_static_iff
  : is_static_arrow A ↔ is_fully_faithful (StaticInterpretF K A)
  := (static_interpret_fully_faithful, static_interpret_static_of_fully_faithful).
Context (H : is_static_arrow A).

(** Factor the interpreter through the existing value-indexed computation
    category. *)

(** 将解释函子经已有值索引计算范畴分解。 *)

Definition StaticRepresentationF
  : Fct (StaticCat (ArrowA K A)) (ComputationCat A)
  := InducedF (StaticInterpretF K A).

(** Reuse the general fully faithful inverse on the indexed image objects. *)

(** 在索引像对象上复用一般完全忠实逆函子。 *)

Definition StaticReifyF
  : Fct (ComputationCat A) (StaticCat (ArrowA K A))
  := FullyFaithfulInverseF (StaticInterpretF K A)
      (static_interpret_fully_faithful H).

(** Reification after interpretation returns the static category up to
    natural isomorphism. *)

(** 解释后恢复，在自然同构意义下返回静态范畴。 *)

Definition StaticRepresentationUnitIso
  : (StaticReifyF ∘F StaticRepresentationF) ≅N (@IdF (StaticCat (ArrowA K A)))
  := FullyFaithfulUnitIso (StaticInterpretF K A)
      (static_interpret_fully_faithful H).

(** Interpretation after reification returns the value-indexed computation
    category. *)

(** 恢复后解释返回值索引计算范畴。 *)

Definition StaticRepresentationCounitIso
  : (StaticRepresentationF ∘F StaticReifyF) ≅N (@IdF (ComputationCat A))
  := FullyFaithfulCounitIso (StaticInterpretF K A)
      (static_interpret_fully_faithful H).

(** The two transparent functors and composite comparisons give an actual
    CatCat equivalence. *)

(** 两个透明函子及其复合比较给出实际 [CatCat] 范畴等价。 *)

Definition StaticRepresentationEq
  : StaticCat (ArrowA K A) ≃C ComputationCat A
  := (StaticRepresentationF; (StaticReifyF;
      (StaticRepresentationUnitIso, StaticRepresentationCounitIso))).

(** Interpreting a recovered arrow returns the original computation. *)

(** 解释恢复后的箭头返回原计算。 *)

Lemma static_representation_β {X Y : @Ob C} (f : Hom (A X) (A Y))
  : static_interpret K A (fmap StaticReifyF f) ≈ f.
Proof.
  exact (fully_faithful_image_preimage (StaticInterpretF K A)
    (static_interpret_fully_faithful H) f).
Qed.

(** Recovering an interpreted arrow returns its static representation. *)

(** 恢复解释后的箭头返回其静态表示。 *)

Lemma static_representation_η {X Y : @Ob C}
    (f : (@Hom (StaticCat (ArrowA K A))) X Y)
  : fmap StaticReifyF (static_interpret K A f) ≈ f.
Proof.
  exact (fully_faithful_preimage_image (StaticInterpretF K A)
    (static_interpret_fully_faithful H) f).
Qed.

(** The inverse functor also preserves the supplied pure inclusion. *)

(** 逆函子也保持所给纯嵌入。 *)

Lemma static_reify_arr {X Y : @Ob C} (f : Hom X Y)
  : fmap StaticReifyF arr[A; f] ≈ static_arr (ArrowA K A) f.
Proof.
  transitivity (fmap StaticReifyF
    (static_interpret K A (static_arr (ArrowA K A) f))).
  - apply functor_fmap_proper. symmetry. exact (static_interpret_arr K A f).
  - apply static_representation_η.
Qed.

(** The recovered global component is exactly the general reification map.
    Keep it abstract before applying it to structured computations. *)

(** 恢复的全局分量恰为一般恢复映射；将其用于结构化计算之前保持此抽象边界。 *)

Lemma static_reify_value {X Y : @Ob C} (f : Hom (A X) (A Y))
  : (fmap StaticReifyF (X := X) (Y := Y) f) tt ≈ arrow_reify A H f.
Proof. reflexivity. Qed.

(** Reification preserves ordinary context, using the general inverse law at
    the same selected product endpoints. *)

(** 恢复在同一组选定积端点处使用一般逆定律，保持通常上下文。 *)

Lemma static_reify_context {X Y : @Ob C} (Z : @Ob C)
    (f : Hom (A X) (A Y))
  : fmap StaticReifyF (X := (Z × X)%ob) (Y := (Z × Y)%ob)
      (context[A; Z; f]) ≈
      static_context (ArrowA K A) Z (fmap StaticReifyF f).
Proof.
  intros [].
  change ((fmap StaticReifyF (X := (Z × X)%ob) (Y := (Z × Y)%ob)
    (context[A; Z; f])) tt ≈
      arr[A; internal_context Z X Y] ∘ (fmap StaticReifyF f) tt).
  etransitivity; [apply static_reify_value |].
  etransitivity; [exact (arrow_reify_context A H Z f) |].
  apply comp_proper; [reflexivity |]. symmetry. apply static_reify_value.
Qed.

End Representation.
