From Cats.Set Require Export
  Morphism.

(** * Magmas on Sets

    A magma supplies only a respectful binary operation. Associativity,
    units and inverses belong to stronger structures. Equality remains
    the setoid's specified Type-valued relation. *)

(** * 广集上的原群

    原群只提供保相等的二元运算，结合律、单位元及逆属于更强结构。
    相等始终是广集指定的 Type 值关系。 *)

(** The algebra family shares one scope. Reserve its multiplication grammar
    before defining the operation; bind its interpretation only after the
    complete magma can supply its own selected evidence. *)

(** 代数运算族共用一个作用域。在定义运算前预留乘法语法；完整原群能够提供
    自己保存的见证后，再绑定唯一的记号解释。 *)

Declare Scope algebra_scope.
Delimit Scope algebra_scope with alg.
Reserved Infix "⋅" (at level 40, left associativity).

(** A chosen respectful multiplication on the supplied setoid. *)

(** 给定广集上的选定保相等乘法。 *)

Minks.Mixin HasMagma (S : SetC)
  :=
  { mul : S → S → S
  ; mul_proper
    :: Proper ([≈S] ==> [≈S] ==> [≈S]) mul
  }.

(** A complete magma owns its setoid and one multiplication extension. *)

(** 完整原群拥有其广集及一份乘法扩充。 *)

Minks.Struct Magma@{u p l}
  extends SetC@{u p}
  with  hasMagma as hasMagma : HasMagma@{l u p}.

Infix "⋅" := (@mul _ (hasMagma _))
: algebra_scope.
Local Open Scope algebra_scope.

(** Left multiplication is respectful without an associativity or unit
    assumption. *)

(** 左乘保持相等，无须结合律或单位元前提。 *)

Program Definition mul_l_resp {M : Magma} (x : M)
  : M →r M
  :=
  {|func y := x ⋅ y
  |}.
Next Obligation.
  intros y z H. rewrite H. reflexivity.
Defined.

(** Right multiplication is respectful under the same weak assumptions. *)

(** 右乘在同样的较弱前提下保持相等。 *)

Program Definition mul_r_resp {M : Magma} (y : M)
  : M →r M
  :=
  {|func x := x ⋅ y
  |}.
Next Obligation.
  intros x z H. rewrite H. reflexivity.
Defined.

(** Sections of multiplication denote respectful maps: [(x ⋅−)] sends
    [y] to [x ⋅ y], and [(−⋅ y)] sends [x] to [x ⋅ y]. The vacant position
    indicates the argument of the map. *)

(** 乘法的偏应用记号表示保相等映射：[(x ⋅−)] 将 [y] 送到 [x ⋅ y]，
    [(−⋅ y)] 将 [x] 送到 [x ⋅ y]；空位表示映射的输入。 *)

Notation "'(' x '⋅−)'" := (mul_l_resp x) : algebra_scope.
Notation "'(−⋅' y ')'" := (mul_r_resp y) : algebra_scope.

(** Left multiplication also respects its fixed factor, using pointwise
    equality of respectful maps rather than equality of function records. *)

(** 左乘也保持固定因子的相等，使用保相等映射的逐点相等，不比较函数记录。 *)

Global Instance mul_l_proper {M : Magma}
  : Proper ([≈S] ==> carrier_equiv (M →S M))
      (λ x : M, (x ⋅−)).
Proof.
  intros x y H z. cbn. rewrite H. reflexivity.
Qed.

(** Right multiplication respects its fixed factor pointwise. *)

(** 右乘逐点保持固定因子的相等。 *)

Global Instance mul_r_proper {M : Magma}
  : Proper ([≈S] ==> carrier_equiv (M →S M))
      (λ y : M, (−⋅ y)).
Proof.
  intros x y H z. cbn. rewrite H. reflexivity.
Qed.
