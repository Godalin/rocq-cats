From Cats Require Export
  Cat.Functor.Product.
From Cats Require Import
  Cat.Core
  Cat.Natural.

(** * Reversing a Mixed-Variance Index

    Exchange the two coordinates while viewing the index category as its
    opposite. The codomain stays unchanged: this differs from [BifunctorOpF],
    which reverses both domain and codomain without exchanging coordinates. *)

(** * 反转混合变元的指标

    将指标范畴视作反范畴并交换两个坐标，值域保持不变。这不同于同时反转定义域
    和值域而不交换坐标的 [BifunctorOpF]。 *)

(** Use the existing pairing and projection functors to exchange coordinates. *)

(** 使用已有配对及投影函子交换坐标。 *)

Definition BifunctorIndexOpF {C D : Cat} (F : Fct ((C^op) ×C C) D)
  : Fct (((C^op)^op) ×C (C^op)) D
  := F ∘F PairF (SndF ((C^op)^op) (C^op))
      (FromDoubleOpF ∘F FstF ((C^op)^op) (C^op)).

(** Reindex a comparison without reversing its direction or its components. *)

(** 重设比较的指标，不反转其方向或分量。 *)

Definition bifunctor_index_op_nt {C D : Cat}
    {F G : Fct ((C^op) ×C C) D} (α : F ⇒ G)
  : BifunctorIndexOpF F ⇒ BifunctorIndexOpF G
  := α ∘Nr PairF (SndF ((C^op)^op) (C^op))
      (FromDoubleOpF ∘F FstF ((C^op)^op) (C^op)).

(** Reindexing respects the original specified component equality. *)

(** 重设指标保持原来指定的分量相等。 *)

Lemma bifunctor_index_op_nt_proper {C D : Cat}
    {F G : Fct ((C^op) ×C C) D} (α β : F ⇒ G) (H : α ≈N β)
  : bifunctor_index_op_nt α ≈N bifunctor_index_op_nt β.
Proof. intros [X Y]. exact (H (Y,X)). Defined.

(** Identity comparisons keep their components. *)

(** 恒等比较保留其分量。 *)

Lemma bifunctor_index_op_nt_id {C D : Cat}
    {F : Fct ((C^op) ×C C) D}
  : bifunctor_index_op_nt (IdN (F := F)) ≈N IdN.
Proof. intros [X Y]. reflexivity. Defined.

(** Vertical composition keeps its order because the codomain is unchanged. *)

(** 值域保持不变，因此竖直复合保留次序。 *)

Lemma bifunctor_index_op_nt_comp {C D : Cat}
    {F G K : Fct ((C^op) ×C C) D} (β : G ⇒ K) (α : F ⇒ G)
  : bifunctor_index_op_nt (β ∘Nv α) ≈N
      (bifunctor_index_op_nt β ∘Nv bifunctor_index_op_nt α).
Proof. intros [X Y]. reflexivity. Defined.

(** The existing right-whiskering theorem retains each computed inverse. *)

(** 已有右须化定理保留每个计算得到的逆。 *)

Definition bifunctor_index_op_nt_NatIso {C D : Cat}
    {F G : Fct ((C^op) ×C C) D} (α : F ⇒ G) (Hα : α ⦂ F ≅N G)
  : bifunctor_index_op_nt α ⦂ BifunctorIndexOpF F ≅N
      BifunctorIndexOpF G
  := nat_whisker_r_iso α (PairF (SndF ((C^op)^op) (C^op))
      (FromDoubleOpF ∘F FstF ((C^op)^op) (C^op))) Hα.
