From Cats Require Export
  Cat.Coend.Core
  Cat.End.IndexReversal.
From Cats Require Import
  Cat.Core
  Cat.Functor.OppositeProduct.

(** * Coends under Reversal of the Index

    All operations below read the same universal end witnesses in the opposite
    codomain, wrapping their test wedges with reversed indices. The codomain
    here stays unchanged, as do each cowedge's legs, selected apex and descent
    witness. No independent dual universal property or choice is introduced. *)

(** * 指标反转下的 Coend

    以下运算在反值域中读取同一泛 end 见证，并反转其测试楔的指标。因此值域不变，
    也保留各余楔的腿、选定顶点和下降见证，不引入独立的对偶泛性质或选择。 *)

(** Read forward end reorientation as cowedge reorientation, rebundling
    only the stored wedge presentation, without equating functor records. *)

(** 将正向 end 重定向读作余楔重定向，只重包装存储的楔表示，不等同函子记录。 *)

Program Definition cowedge_index_op {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {W} (κ : Cowedge F W)
  : Cowedge (BifunctorIndexOpF F) W
  :=
  {|op_wedge :=
      {|wedge_leg X := wedge_index_op (op_wedge κ) X
      |}
  |}.
Next Obligation. exact (wedge_comm (wedge_index_op (op_wedge κ)) f). Defined.

(** The backward wrapper retains the stored legs and reverses the same end
    commuting equation. *)

(** 反向包装保留存储的腿，并反转同一 end 交换方程。 *)

Program Definition cowedge_index_unop {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {W}
    (κ : Cowedge (BifunctorIndexOpF F) W)
  : Cowedge F W
  :=
  {|op_wedge :=
      {|wedge_leg X := κ X
      |}
  |}.
Next Obligation. symmetry. exact (wedge_comm (op_wedge κ) f). Defined.

(** ** Equality and Round Trips

    Fix the diagram and apex. Reuse the opposite wedges' pointwise laws;
    no equality of the cowedge records is asserted. *)

(** ** 相等及往返

    固定图式和顶点，复用反楔的逐点定律，不声称余楔记录相等。 *)

Section CowedgeLaws.
Context {C D : Cat} {F : Fct ((C^op) ×C C) D} {W : @Ob D}.

(** Forward reorientation preserves specified cowedge equality. *)

(** 正向重定向保持指定余楔相等。 *)

Lemma cowedge_index_op_proper (κ μ : Cowedge F W) (H : κ ≈CW μ)
  : cowedge_index_op κ ≈CW cowedge_index_op μ.
Proof. exact H. Defined.

(** Backward reorientation preserves the same equality. *)

(** 反向重定向保持同一相等。 *)

Lemma cowedge_index_unop_proper
    (κ μ : Cowedge (BifunctorIndexOpF F) W) (H : κ ≈CW μ)
  : cowedge_index_unop κ ≈CW cowedge_index_unop μ.
Proof. exact H. Defined.

(** Forward then backward retains the original legs. *)

(** 正向再反向保留原腿。 *)

Lemma cowedge_index_op_inv_l (κ : Cowedge F W)
  : cowedge_index_unop (cowedge_index_op κ) ≈CW κ.
Proof. intros X. reflexivity. Defined.

(** Backward then forward retains the supplied opposite-index legs. *)

(** 反向再正向保留给定反指标腿。 *)

Lemma cowedge_index_op_inv_r (κ : Cowedge (BifunctorIndexOpF F) W)
  : cowedge_index_op (cowedge_index_unop κ) ≈CW κ.
Proof. intros X. reflexivity. Defined.

End CowedgeLaws.

(** Universality is the end witness's reorientation in the opposite codomain. *)

(** 泛性质就是反值域中 end 见证的重定向。 *)

Definition coend_index_op_universal {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {E} {κ : Cowedge F E}
    (Hκ : is_coend κ)
  : is_coend (cowedge_index_op κ)
  := λ W μ, Hκ W (op_wedge (cowedge_index_unop {|op_wedge := μ|})).

(** Read the original universal end witness using the forward test wrapper. *)

(** 使用正向测试包装读取原来的泛 end 见证。 *)

Definition coend_index_unop_universal {C D : Cat}
    {F : Fct ((C^op) ×C C) D} {E}
    {κ : Cowedge (BifunctorIndexOpF F) E} (Hκ : is_coend κ)
  : is_coend (cowedge_index_unop κ)
  := λ W μ, Hκ W (op_wedge (cowedge_index_op {|op_wedge := μ|})).

(** Explicitly reorient the stored opposite end, keeping its selected apex. *)

(** 显式重定向存储的反 end，保持其选定顶点。 *)

Program Definition CoendIndexOp {C D : Cat}
    {F : Fct ((C^op) ×C C) D} `{HC : !HasCoend D F}
  : HasCoend D (BifunctorIndexOpF F)
  :=
  {|hasOpEnd :=
      {|EndObj := coend[F]
      ; end_wedge := op_wedge (cowedge_index_op ιcoend[F])
      ; end_universal := coend_index_op_universal (coend_universal F)
      |}
  |}.

(** The backward choice also stores only the transported opposite end. *)

(** 反向选择同样只存储运输后的反 end。 *)

Program Definition CoendIndexUnop {C D : Cat}
    {F : Fct ((C^op) ×C C) D}
    `{HC : !HasCoend D (BifunctorIndexOpF F)}
  : HasCoend D F
  :=
  {|hasOpEnd :=
      {|EndObj := coend[BifunctorIndexOpF F]
      ; end_wedge := op_wedge
          (cowedge_index_unop ιcoend[BifunctorIndexOpF F])
      ; end_universal := coend_index_unop_universal
          (coend_universal (BifunctorIndexOpF F))
      |}
  |}.

(** Descending after forward reorientation uses the original end mediator
    with the backward cowedge wrapper. *)

(** 正向重定向后的下降将原 end 中介用于反向余楔包装。 *)

Lemma coend_index_op_desc {C D : Cat}
    {F : Fct ((C^op) ×C C) D} `{HC : !HasCoend D F} {W}
    (κ : Cowedge (BifunctorIndexOpF F) W)
  : @coend_desc (C^op) D (BifunctorIndexOpF F) CoendIndexOp W κ
      ≈ coend⟨cowedge_index_unop κ⟩.
Proof. reflexivity. Defined.

(** Descending after backward reorientation uses the forward wrapper. *)

(** 反向重定向后的下降使用正向包装。 *)

Lemma coend_index_unop_desc {C D : Cat}
    {F : Fct ((C^op) ×C C) D}
    `{HC : !HasCoend D (BifunctorIndexOpF F)} {W} (κ : Cowedge F W)
  : @coend_desc C D F CoendIndexUnop W κ
      ≈ coend⟨cowedge_index_op κ⟩.
Proof. reflexivity. Defined.
