From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Monoidal.Bifct
  Instance.Set.Core
  Cat.Monoidal.Laws.
From Cats Require Export
  Cat.Day.Semigroupal.
From Cats Require Export Cat.Monoidal.Monoidal (HasMonoidal_interchange).

Local Open Scope monoidal_scope.
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
    (A : Tensor3LF T ≅N Tensor3RF T)
    (L : AtLF T I ≅N IdF) (R : AtRF T I ≅N IdF).
Context (Hp : is_tensor_pentagon T A).
Context (Ht : ∀ X Y : @Ob C,
    fmap T (X := (X,T (I,Y))) (Y := (X,Y)) (id,L.1 Y) ∘
      A.1 ((X,I),Y) ≈
    fmap T (X := (T (X,I),Y)) (Y := (X,Y)) (R.1 X,id)).
Context `(HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}), HasDay C T F G).

(** Reuse the tensor, representable unit, natural isomorphisms and their
    computed inverses. Interchange is inherited from the tensor bifunctor. *)

(** 复用张量、可表单位、自然同构及其计算逆；交换律继承自张量双函子。 *)

Definition DayMonoidal
  : HasMonoidal (FctCat C (SetCat@{u p _ _ _ _ _}))
  := BifctHasMonoidal (DayTensorF T HD) (DayUnitF I)
      (DayAssociatorFct T HD A)
      (DayLeftUnitorFct T HD L) (DayRightUnitorFct T HD R)
      (λ F G H K, day_pentagon T A Hp F G H K)
      (λ F G, day_triangle T A L R Ht F G).

(** The reconstructed tensor map agrees with the supplied Day bifunctor
    action in natural equality, without equality of functor records. *)

(** 重建张量映射在自然相等下等于给定 Day 双函子作用，无需函子记录相等。 *)

Lemma day_monoidal_map {F F' G G' : Fct C (SetCat@{u p _ _ _ _ _})}
    (α : F ⇒ F') (β : G ⇒ G')
  : tensor_map (IM := HasMonoidal_interchange DayMonoidal)
      (X := F) (X' := F') (Y := G) (Y' := G') α β ≈N
      @DayMapN C T F F' G G' (HD F G) (HD F' G') α β.
Proof.
  exact (@bifct_sequence (FctCat C SetCat) (DayTensorF T HD)
    F F' G G' α β).
Defined.

(** Identity components compare the derived tensor functor with the
    original Day tensor. The chosen coends and structural inverses stay fixed. *)

(** 恒等分量比较导出的张量函子与原 Day 张量，保持选定 coend 与结构逆不变。 *)

Definition DayTensorIso
  : tensorF (HasMonoidal_interchange DayMonoidal) ≅N DayTensorF T HD.
Proof.
  unfold DayMonoidal.
  apply (@bifct_tensor_iso (FctCat C SetCat) (DayTensorF T HD)).
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
Context {C : Cat} (MC : HasMonoidal C)
    (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}),
      HasDay C (tensorF (HasMonoidal_interchange MC)) F G).

(** The inherited pentagon and triangle enable the full Day structure. *)

(** 继承的五边形与三角形启用完整 Day 结构。 *)

Definition MonoidalDay
  : HasMonoidal (FctCat C (SetCat@{u p _ _ _ _ _}))
  := DayMonoidal (tensorF (HasMonoidal_interchange MC)) (𝐈[MC])
      (TensorAssocIsoN (IM := HasMonoidal_interchange MC) (AC := MC))
      (TensorUnitorLIsoN (IM := HasMonoidal_interchange MC) (UC := MC))
      (TensorUnitorRIsoN (IM := HasMonoidal_interchange MC) (UC := MC))
      (tensor_pentagon (IM := HasMonoidal_interchange MC) (AC := MC))
      (tensor_map_triangle (IM := HasMonoidal_interchange MC)
        (IP := HasMonoidal_isPremonoidal MC)) HD.

End MonoidalBase.
