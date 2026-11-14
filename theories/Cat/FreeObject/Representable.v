From Cats Require Export
  Cat.FreeObject.Adjunction.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift
  Instance.Set.Representable.

(** * Free Objects and Pointwise Representability

    Lift source hom-sets into a common ambient size. Representing hom-sets
    are lifted separately by [Rep↑]; their native carrier and equality sizes
    remain independent. The comma/adjunction theorem itself needs no such
    common-size assumption. *)

(** * 自由对象与逐点可表性

    将源 Hom 广集提升到共同环境大小；表示 Hom 广集由 [Rep↑] 单独提升，因此
    原生载体与相等大小保持独立。逗号／伴随定理本身不需要共同大小的假设。 *)

Definition FreeHomF@{u p +} {C D : Cat} (U : Fct D C) (X : @Ob C)
  : Fct D SetCat@{u p _ _ _ _ _}
  := LiftF ∘F (Hom(X,-) ∘F U).

(** ** Representing Universal Arrows

    Fix [U : Fct D C] and ambient value universes [u], [p]. Compare
    universal arrows with universal elements of lifted hom functors, leading
    to the pointwise representability criterion for a left adjoint. *)

(** ** 表示泛箭头

    固定 [U : Fct D C] 及环境值宇宙 [u]、[p]，比较泛箭头与提升 Hom 函子的泛元素，进而给出左伴随的逐点可表性判据。 *)

Section FreeRepresentations.
Universe u p.
Context {C D : Cat} (U : Fct D C).

(** A universal arrow is the universal element of its lifted hom functor. *)

(** 泛箭头就是其提升 Hom 函子的泛元素。 *)

Definition universal_arrow_element {X : @Ob C} {A : @Ob D}
    {η : Hom X (U A)} (Hη : η ⦂ UnivArr(U))
  : {|lower := η|} ⦂ Univ(
      (FreeHomF U X : Fct D SetCat@{u p _ _ _ _ _})).
Proof.
  intros B [f]. destruct (Hη B f) as [g Hg]. exists g.
  refine {|this := {|lower := @this _ _ _ _ _ Hg|}
          ; that := _
          |}.
  intros k Hk. exact (@that _ _ _ _ _ Hg k (lower Hk)).
Defined.

(** Unwrapping a universal element recovers the direct universal arrow. *)

(** 拆开泛元素恢复直接泛箭头。 *)

Definition universal_element_arrow {X : @Ob C} {A : @Ob D}
    {η : (FreeHomF U X : Fct D SetCat@{u p _ _ _ _ _}) A}
    (Hη : η ⦂ Univ(FreeHomF U X))
  : lower η ⦂ UnivArr(U).
Proof.
  intros B f. destruct (Hη B {|lower := f|}) as [g Hg]. exists g.
  refine {|this := _
          ; that := _
          |}.
  - exact (lower (@this _ _ _ _ _ Hg)).
  - intros k Hk. apply (@that _ _ _ _ _ Hg k).
    exact {|lower := Hk|}.
Defined.

(** The general universal-element theorem supplies the representation;
    no second Yoneda proof is needed for free objects. *)

(** 一般泛元素定理给出表示，自由对象无需第二份 Yoneda 证明。 *)

Definition universal_arrow_representation {X : @Ob C} {A : @Ob D}
    {η : Hom X (U A)} (Hη : η ⦂ UnivArr(U))
  : A ⦂ Rep↑ (FreeHomF U X : Fct D SetCat@{u p _ _ _ _ _})
  := universal_element_lifted_representation _ (universal_arrow_element Hη).

(** The generic element of a representation gives the candidate unit. *)

(** 表示的泛元素给出候选单位。 *)

Definition representation_universal_arrow {X : @Ob C} {A : @Ob D}
    (R : A ⦂ Rep↑ (FreeHomF U X : Fct D SetCat@{u p _ _ _ _ _}))
  : ∃ η : Hom X (U A), η ⦂ UnivArr(U).
Proof.
  exists (lower (lifted_representation_generic _ R)).
  exact (universal_element_arrow (lifted_representation_universal _ R)).
Defined.

(** Pointwise representations assemble selected initial structured arrows. *)

(** 逐点表示组装为选定始结构箭头。 *)

Definition PointwiseFreeObj
    (R : ∀ X : @Ob C, ∃ A : @Ob D,
      A ⦂ Rep↑ (FreeHomF U X : Fct D SetCat@{u p _ _ _ _ _}))
  : HasFreeObj U
  := FreeObjFromUniversal U (λ X, (R X).1)
      (λ X, (representation_universal_arrow (R X).2).1)
      (λ X, (representation_universal_arrow (R X).2).2).

(** Pointwise representability and having a selected left adjoint carry
    equivalent data. Only this representation packaging uses common sizes. *)

(** 逐点可表性与具有选定左伴随携带等价数据；只有表示的包装使用共同大小。 *)

Theorem pointwise_representable_iff_left_adjoint
  : (∀ X : @Ob C, ∃ A : @Ob D,
      A ⦂ Rep↑ (FreeHomF U X : Fct D SetCat@{u p _ _ _ _ _}))
      ↔ ∃ F : Fct C D, F ⊣ U.
Proof.
  split.
  - intros R. apply (fst (free_objects_iff_left_adjoint U)).
    exact (PointwiseFreeObj R).
  - intros [F A] X. exists (F X).
    apply (universal_arrow_representation (η := adj_unit A X)).
    exact (@free_universal C D U (AdjFreeObj A) X).
Defined.

End FreeRepresentations.

(** The right-adjoint representation criterion is the same theorem in the
    opposite categories. Its hom functor has values [Hom(U(-),X)]. *)

(** 右伴随的表示判据就是反范畴中的同一定理，其 Hom 函子取值为 [Hom(U(-),X)]。 *)

Theorem pointwise_representable_iff_right_adjoint@{u p +}
    {C D : Cat} (U : Fct D C)
  : (∀ X : @Ob C, ∃ A : @Ob D,
      A ⦂ Rep↑ (FreeHomF (U^opF) X :
        Fct (D^op) SetCat@{u p _ _ _ _ _}))
      ↔ ∃ R : Fct C D, U ⊣ R.
Proof.
  split.
  - intros H. apply (fst (free_objects_op_iff_right_adjoint U)).
    exact (PointwiseFreeObj (U^opF) H).
  - intros [R A].
    apply (snd (pointwise_representable_iff_left_adjoint (U^opF))).
    exists (R^opF). exact (OpAdj A).
Defined.
