From Cats Require Import
  Cat.Monoidal.Bifct
  Instance.Set.Core.
From Cats Require Export
  Cat.Day.Coherence.

(** * Semigroupal Day Convolution

    Uniform chosen convolutions carry the lifted associator of a
    semigroupal tensor. The Day pentagon supplies coherence. *)

(** * 半群 Day 卷积

    统一选定的卷积继承半群张量提升后的结合子，其相干性来自 Day 五边形。 *)

(** Assemble the convolution tensor from a base associator and its pentagon. *)

(** 从基范畴的结合子和五边形装配卷积张量。 *)

Definition DaySemigroupal {C : Cat} (T : Fct (C ×C C) C)
    (A : Tensor3LF T ≅N Tensor3RF T) (Hp : is_tensor_pentagon T A)
    `(HD : ∀ F G : Fct C SetCat, HasDay C T F G)
  : HasAssoc (FctCat C SetCat) (BifctHasBinoidal (DayTensorF T HD))
  := BifctHasAssoc (DayTensorF T HD) (DayAssociatorFct T HD A)
      (λ F G H K, day_pentagon T A Hp F G H K).

(** Lift associativity for a fixed tensor with interchange. *)

(** 提升具有交换律的固定张量的结合性。 *)

Definition SemigroupalDay {C : Cat}
    {BC : HasBinoidal C} (IM : IsMagmoidal BC)
    (AC : HasAssoc C BC)
    (HD : ∀ F G : Fct C SetCat, HasDay C (tensorF IM) F G)
  : HasAssoc (FctCat C SetCat)
      (BifctHasBinoidal (DayTensorF (tensorF IM) HD))
  := DaySemigroupal (tensorF IM) (TensorAssocIsoN (IM := IM) (AC := AC))
      (tensor_pentagon (IM := IM) (AC := AC)) HD.
