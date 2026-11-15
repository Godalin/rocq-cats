From Cats Require Export
  Cat.End.Core
  Cat.Functor.IndexReversal.
From Cats Require Import
  Cat.Core
  Cat.Natural.

(** * Ends under Reversal of the Index

    Reverse only the index, exchanging the two mixed-variance coordinates.
    Wedges retain their legs and apex. Their commuting equation is read in
    reverse; an existing universal witness supplies the same factoring maps.
    No equality of functor records or law witnesses is required. *)

(** * 指标反转下的 End

    只反转指标并交换两个混合变元坐标。楔保留腿和顶点，反向读取其交换方程，
    由已有泛见证提供同一分解映射，不要求函子记录或定律见证相等。 *)

(** Reinterpret the same legs over the opposite index. *)

(** 将同一组腿重新解释在反指标上。 *)

Program Definition wedge_index_op {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {W} (κ : Wedge F W)
  : Wedge (BifunctorIndexOpF F) W
  :=
  {|wedge_leg X := κ X
  |}.
Next Obligation. symmetry. exact (wedge_comm κ f). Defined.

(** Recover the original presentation without equating the double-flipped
    functor record with the original one. *)

(** 恢复原表示，不等同两次翻转的函子记录与原记录。 *)

Program Definition wedge_index_unop {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {W}
    (κ : Wedge (BifunctorIndexOpF F) W)
  : Wedge F W
  :=
  {|wedge_leg X := κ X
  |}.
Next Obligation. symmetry. exact (wedge_comm κ f). Defined.

(** ** Pointwise Laws of the Two Presentations

    Fix a diagram and an apex. Both wrappers retain the exact legs, so their
    respectfulness and inverse laws use only the original Hom equality. *)

(** ** 两种表示的逐点定律

    固定图式和顶点。两个包装保留原腿，因此其保持性和互逆律只使用原 Hom 相等。 *)

Section WedgeLaws.
Context {C D : Cat} {F : Fct ((C^op) ×C C) D} {W : @Ob D}.

(** Forward reorientation respects wedge equality. *)

(** 正向重定向保持楔相等。 *)

Lemma wedge_index_op_proper (κ μ : Wedge F W) (H : κ ≈W μ)
  : wedge_index_op κ ≈W wedge_index_op μ.
Proof. exact H. Defined.

(** Backward reorientation respects the same equality. *)

(** 反向重定向保持同一相等。 *)

Lemma wedge_index_unop_proper
    (κ μ : Wedge (BifunctorIndexOpF F) W) (H : κ ≈W μ)
  : wedge_index_unop κ ≈W wedge_index_unop μ.
Proof. exact H. Defined.

(** Reorientation and its wrapper recover the original legs. *)

(** 重定向及反向包装恢复原腿。 *)

Lemma wedge_index_op_inv_l (κ : Wedge F W)
  : wedge_index_unop (wedge_index_op κ) ≈W κ.
Proof. intros X. reflexivity. Defined.

(** The reverse round trip also recovers the supplied legs. *)

(** 反向往返也恢复给定的腿。 *)

Lemma wedge_index_op_inv_r (κ : Wedge (BifunctorIndexOpF F) W)
  : wedge_index_op (wedge_index_unop κ) ≈W κ.
Proof. intros X. reflexivity. Defined.

End WedgeLaws.

(** A universal wedge retains the same factorization witness when queried
    with a reoriented test wedge; no second uniqueness proof is built. *)

(** 泛楔接受重定向的测试楔时保留同一分解见证，不另建唯一性证明。 *)

Definition end_index_op_universal {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {E} {κ : Wedge F E} (Hκ : is_end κ)
  : is_end (wedge_index_op κ)
  := λ W μ, Hκ W (wedge_index_unop μ).

(** Read that same universal witness back in the original presentation. *)

(** 在原表示中读回同一泛见证。 *)

Definition end_index_unop_universal {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {E}
    {κ : Wedge (BifunctorIndexOpF F) E} (Hκ : is_end κ)
  : is_end (wedge_index_unop κ)
  := λ W μ, Hκ W (wedge_index_op μ).

(** Explicitly reorient a chosen end, retaining its apex and original
    factorization function. Import does not enable this choice globally. *)

(** 显式重定向选定 end，保留其顶点和原分解函数；导入不全局启用此选择。 *)

Program Definition EndIndexOp {C D : Cat}
    {F : Fct ((C^op) ×C C) D} `{HE : !HasEnd D F}
  : HasEnd D (BifunctorIndexOpF F)
  :=
  {|EndObj := end[F]
  ; end_wedge := wedge_index_op πend[F]
  ; end_universal := end_index_op_universal (end_universal F)
  |}.

(** The backward wrapper retains the given end's selected apex as well. *)

(** 反向包装同样保留给定 end 的选定顶点。 *)

Program Definition EndIndexUnop {C D : Cat}
    {F : Fct ((C^op) ×C C) D}
    `{HE : !HasEnd D (BifunctorIndexOpF F)}
  : HasEnd D F
  :=
  {|EndObj := end[BifunctorIndexOpF F]
  ; end_wedge := wedge_index_unop πend[BifunctorIndexOpF F]
  ; end_universal := end_index_unop_universal
      (end_universal (BifunctorIndexOpF F))
  |}.

(** The reoriented mediator is the original mediator applied to the
    backward test-wedge wrapper, without changing its computational witness. *)

(** 重定向中介就是将原中介用于反向测试楔包装，不改变其计算见证。 *)

Lemma end_index_op_lift {C D : Cat}
    {F : Fct ((C^op) ×C C) D} `{HE : !HasEnd D F} {W}
    (κ : Wedge (BifunctorIndexOpF F) W)
  : @end_lift (C^op) D (BifunctorIndexOpF F) EndIndexOp W κ
      ≈ end⟨wedge_index_unop κ⟩.
Proof. reflexivity. Defined.

(** Backward transport uses the original mediator on the forward wrapper. *)

(** 反向运输将原中介用于正向包装。 *)

Lemma end_index_unop_lift {C D : Cat}
    {F : Fct ((C^op) ×C C) D}
    `{HE : !HasEnd D (BifunctorIndexOpF F)} {W} (κ : Wedge F W)
  : @end_lift C D F EndIndexUnop W κ ≈ end⟨wedge_index_op κ⟩.
Proof. reflexivity. Defined.
