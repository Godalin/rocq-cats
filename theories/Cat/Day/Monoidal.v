From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Binoidal.Bifunctor
  Cat.Monoidal.Bifunctor
  Instance.Set.Core.
From Cats Require Export
  Cat.Day.Coherence.

(** * The Day Monoidal Category *)

(** * Day 幺半范畴 *)

(** ** Assembly under Explicit Coherence and Existence

    A coherent base bifunctor and uniform selected convolutions suffice.
    Existence remains an input: importing this module makes no global
    choice and does not assert that all sizes admit self-indexed coends. *)

(** ** 在显式相干与存在条件下装配

    相干的基双函子和统一选定卷积已足够。存在性仍是输入：导入本模块不进行
    全局选择，也不声称所有大小都允许自索引 coend。 *)

Section DayMonoidal.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C) (I : @Ob C)
    (A : TensorLeftF T ≅N TensorRightF T)
    (L : π2F T I ≅N IdF) (R : π1F T I ≅N IdF).
Context (Hp : ∀ a b c d : @Ob C,
    A.1 ((a,b),T (c,d)) ∘ A.1 ((T (a,b),c),d) ≈
      fmap T (X := (a,T (T (b,c),d))) (Y := (a,T (b,T (c,d))))
        (id,A.1 ((b,c),d)) ∘
      (A.1 ((a,T (b,c)),d) ∘
        fmap T (X := (T (T (a,b),c),d)) (Y := (T (a,T (b,c)),d))
          (A.1 ((a,b),c),id))).
Context (Ht : ∀ X Y : @Ob C,
    fmap T (X := (X,T (I,Y))) (Y := (X,Y)) (id,L.1 Y) ∘
      A.1 ((X,I),Y) ≈
    fmap T (X := (T (X,I),Y)) (Y := (X,Y)) (R.1 X,id)).
Context (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}), HasDay C T F G).
Local Existing Instance HD.

(** Reuse the tensor, representable unit, natural isomorphisms and their
    computed inverses. Interchange is inherited from the tensor bifunctor. *)

(** 复用张量、可表单位、自然同构及其计算逆；交换律继承自张量双函子。 *)

Definition DayMonoidal
  : MonoidalCat (FctCat C (SetCat@{u p _ _ _ _ _})).
Proof.
  refine (BifunctorMonoidal (DayTensorF T HD) (DayUnitF I)
    (DayAssociatorFct T HD A)
    (DayLeftUnitorFct T HD L) (DayRightUnitorFct T HD R) _ _).
  - intros F G H K. exact (day_pentagon T A Hp F G H K).
  - intros F G. exact (day_triangle T A L R Ht F G).
Defined.

(** The reconstructed tensor map agrees with the supplied Day bifunctor
    action in natural equality, without equality of functor records. *)

(** 重建张量映射在自然相等下等于给定 Day 双函子作用，无需函子记录相等。 *)

Lemma day_monoidal_map {F F' G G' : Fct C (SetCat@{u p _ _ _ _ _})}
    (α : F ⇒ F') (β : G ⇒ G')
  : @tensor_map _ DayMonoidal F F' G G' α β ≈N
      @DayMapN C T F F' G G' (HD F G) (HD F' G') α β.
Proof.
  exact (@bifunctor_sequence (FctCat C SetCat) (DayTensorF T HD)
    F F' G G' α β).
Defined.

(** Identity components compare the derived tensor functor with the
    original Day tensor. The chosen coends and structural inverses stay fixed. *)

(** 恒等分量比较导出的张量函子与原 Day 张量，保持选定 coend 与结构逆不变。 *)

Definition DayTensorIso
  : tensorF DayMonoidal ≅N DayTensorF T HD.
Proof.
  unfold DayMonoidal.
  apply (@bifunctor_monoidal_iso (FctCat C SetCat) (DayTensorF T HD)).
Defined.

End DayMonoidal.

(** ** Starting from an Existing Monoidal Category

    Retain the supplied category's tensor, unit and structural inverses.
    Its derived bimap coherence already has exactly the hypotheses required
    above. Only convolution existence must still be supplied explicitly. *)

(** ** 从已有幺半范畴出发

    保留给定范畴的张量、单位和结构逆。其导出二元映射的相干律恰好提供上述
    假设；只需再显式提供卷积存在性。 *)

Section MonoidalBase.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C)
    (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}),
      HasDay C (tensorF MC) F G).

(** The inherited pentagon and triangle enable the full Day structure. *)

(** 继承的五边形与三角形启用完整 Day 结构。 *)

Definition MonoidalDay
  : MonoidalCat (FctCat C (SetCat@{u p _ _ _ _ _}))
  := DayMonoidal (tensorF MC) (TensorUnit MC)
      (@monoidal_associator C MC)
      (@monoidal_left_unitor C MC) (@monoidal_right_unitor C MC)
      (@monoidal_pentagon C MC) (@monoidal_triangle C MC) HD.

End MonoidalBase.
