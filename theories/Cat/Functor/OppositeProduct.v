From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Opposites of Product Domains *)

(** * 积定义域的反范畴 *)

(** The identity on pairs compares a product of opposites with the opposite
    product. It does not identify category records or their law witnesses. *)

(** 对象对上的恒等将反范畴的积比较到积的反范畴，不要求范畴记录或定律见证相等。 *)

Program Definition ProductOpF (C D : Cat)
  : Functor ((C^op) ×C (D^op)) ((C ×C D)^op)
  :=
  {|F0 X := X
  ; F1 X Y f := f
  |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. split; reflexivity. Qed.
Next Obligation. split; reflexivity. Qed.

(** Reverse a mixed-variance bifunctor in both its domain and codomain.
    The indexing category becomes [C^op]; object pairs are not exchanged. *)

(** 同时反转混合变元双函子的定义域和值域。指标范畴变为 [C^op]，不交换对象对。 *)

Definition BifunctorOpF {C D : Cat} (F : Functor ((C^op) ×C C) D)
  : Functor (((C^op)^op) ×C (C^op)) (D^op)
  := F^opF ∘F ProductOpF (C^op) C.

(** Taking opposites reverses ordinary natural transformations of these
    bifunctors. This is whiskering of the existing opposite transformation. *)

(** 取反反转这些双函子间的普通自然变换，直接使用已有反自然变换的须化。 *)

Definition bifunctor_op_nt {C D : Cat}
    {F G : Functor ((C^op) ×C C) D} (α : F ⇒ G)
  : BifunctorOpF G ⇒ BifunctorOpF F
  := α^opN ∘Nr ProductOpF (C^op) C.

(** The opposite transformation respects componentwise equality. *)

(** 反自然变换保持分量相等。 *)

Global Instance bifunctor_op_nt_proper {C D : Cat}
    {F G : Functor ((C^op) ×C C) D}
  : Proper (NatEq ==> NatEq) (@bifunctor_op_nt C D F G).
Proof. intros α β H [X Y]. exact (H (X, Y)). Qed.

(** Identity transformations remain identities after reversing variance. *)

(** 反转变元后恒等自然变换仍为恒等。 *)

Lemma bifunctor_op_nt_id {C D : Cat} {F : Functor ((C^op) ×C C) D}
  : bifunctor_op_nt (idN (F := F)) ≈N idN.
Proof. intros [X Y]. reflexivity. Qed.

(** Reversing variance reverses vertical composition. *)

(** 反转变元反转垂直复合。 *)

Lemma bifunctor_op_nt_comp {C D : Cat}
    {F G K : Functor ((C^op) ×C C) D} (β : G ⇒ K) (α : F ⇒ G)
  : bifunctor_op_nt (β ∘Nv α)
    ≈N (bifunctor_op_nt α ∘Nv bifunctor_op_nt β).
Proof. intros [X Y]. reflexivity. Qed.

(** Taking opposites retains the component inverses of a natural isomorphism. *)

(** 取反保留自然同构的分量逆。 *)

Definition bifunctor_op_nt_NatIso {C D : Cat}
    {F G : Functor ((C^op) ×C C) D} (α : F ⇒ G) (Hα : α ⦂ F ≅N G)
  : bifunctor_op_nt α ⦂ BifunctorOpF G ≅N BifunctorOpF F.
Proof. intros [X Y]. exact (nt_op_NatIso α Hα (X, Y)). Defined.
