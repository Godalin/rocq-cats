From Cats.Set Require Export
  Morphism.

(** * Magmas on Sets

    A magma supplies only a respectful binary operation. Associativity,
    units and inverses belong to stronger structures. Equality remains
    the setoid's specified Type-valued relation. *)

(** * 广集上的原群

    原群只提供保相等的二元运算，结合律、单位元及逆属于更强结构。
    相等始终是广集指定的 Type 值关系。 *)

Class Magma (M : SetC)
  :=
  (** Compute the underlying setoid from the named parameter. *)

  (** 由具名参数计算底层广集。 *)

  { MagmaS :> SetC := M

  (** Store multiplication once, together with its respectfulness. *)

  (** 只保存一次乘法及其保相等性。 *)

  ; magma_mul : M → M → M
  ; magma_mul_proper
    :: Proper (carrier_equiv M ==> carrier_equiv M ==> carrier_equiv M)
        magma_mul
  }.

Arguments MagmaS {_} _.

Declare Scope magma_scope.
Delimit Scope magma_scope with magma.
Infix "⋅" := magma_mul (at level 40, left associativity) : magma_scope.
Local Open Scope magma_scope.

(** Left multiplication is respectful without an associativity or unit
    assumption. *)

(** 左乘保持相等，无须结合律或单位元前提。 *)

Program Definition magma_mul_l_resp {M : SetC} `{HM : !Magma M} (x : M)
  : M →r M
  :=
  {|func y := x ⋅ y
  |}.
Next Obligation.
  intros y z H. apply magma_mul_proper; [reflexivity | exact H].
Defined.

(** Right multiplication is respectful under the same weak assumptions. *)

(** 右乘在同样的较弱前提下保持相等。 *)

Program Definition magma_mul_r_resp {M : SetC} `{HM : !Magma M} (y : M)
  : M →r M
  :=
  {|func x := x ⋅ y
  |}.
Next Obligation.
  intros x z H. apply magma_mul_proper; [exact H | reflexivity].
Defined.

(** Left multiplication also respects its fixed factor, using pointwise
    equality of respectful maps rather than equality of function records. *)

(** 左乘也保持固定因子的相等，使用保相等映射的逐点相等，不比较函数记录。 *)

Global Instance magma_mul_l_proper {M : SetC} `{HM : !Magma M}
  : Proper (carrier_equiv M ==> carrier_equiv (M →S M)) magma_mul_l_resp.
Proof.
  intros x y H z. apply magma_mul_proper; [exact H | reflexivity].
Qed.

(** Right multiplication respects its fixed factor pointwise. *)

(** 右乘逐点保持固定因子的相等。 *)

Global Instance magma_mul_r_proper {M : SetC} `{HM : !Magma M}
  : Proper (carrier_equiv M ==> carrier_equiv (M →S M)) magma_mul_r_resp.
Proof.
  intros x y H z. apply magma_mul_proper; [reflexivity | exact H].
Qed.
