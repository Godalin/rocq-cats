From Cats.Set Require Export
  Morphism.

(** * Magmas on Sets

    A magma supplies only a respectful binary operation. Associativity,
    units and inverses belong to stronger structures. Equality remains
    the setoid's specified Type-valued relation. *)

(** * 广集上的原群

    原群只提供保相等的二元运算，结合律、单位元及逆属于更强结构。
    相等始终是广集指定的 Type 值关系。 *)

(** A chosen respectful multiplication on the supplied setoid. *)

(** 给定广集上的选定保相等乘法。 *)

Class HasMagma (S : SetC)
  :=
  { magma_mul : S → S → S
  ; magma_mul_proper
    :: Proper (carrier_equiv S ==> carrier_equiv S ==> carrier_equiv S)
        magma_mul
  }.

(** A complete magma owns its setoid and one multiplication extension. *)

(** 完整原群拥有其广集及一份乘法扩充。 *)

Record Magma@{u p l}
  :=
  { MagmaS :> SetC@{u p}
  ; hasMagma :: HasMagma@{l u p} MagmaS
  }.

(** Pack a fixed-setoid choice without copying its multiplication. *)

(** 将固定广集上的选择打包，不复制乘法。 *)

Program Definition MagmaFromExtension (S : SetC) (HM : HasMagma S)
  : Magma
  :=
  {|MagmaS := S
  ; hasMagma := HM
  |}.

Declare Scope magma_scope.
Delimit Scope magma_scope with magma.
Infix "⋅" := (@magma_mul _ (hasMagma _))
  (at level 40, left associativity) : magma_scope.
Local Open Scope magma_scope.

(** Left multiplication is respectful without an associativity or unit
    assumption. *)

(** 左乘保持相等，无须结合律或单位元前提。 *)

Program Definition magma_mul_l_resp {M : Magma} (x : M)
  : M →r M
  :=
  {|func y := x ⋅ y
  |}.
Next Obligation.
  intros y z H. apply (@magma_mul_proper _ (hasMagma M)); [reflexivity | exact H].
Defined.

(** Right multiplication is respectful under the same weak assumptions. *)

(** 右乘在同样的较弱前提下保持相等。 *)

Program Definition magma_mul_r_resp {M : Magma} (y : M)
  : M →r M
  :=
  {|func x := x ⋅ y
  |}.
Next Obligation.
  intros x z H. apply (@magma_mul_proper _ (hasMagma M)); [exact H | reflexivity].
Defined.

(** Sections of multiplication denote respectful maps: [(x ⋅−)] sends
    [y] to [x ⋅ y], and [(−⋅ y)] sends [x] to [x ⋅ y]. The vacant position
    indicates the argument of the map. *)

(** 乘法的偏应用记号表示保相等映射：[(x ⋅−)] 将 [y] 送到 [x ⋅ y]，
    [(−⋅ y)] 将 [x] 送到 [x ⋅ y]；空位表示映射的输入。 *)

Notation "'(' x '⋅−)'" := (magma_mul_l_resp x) : magma_scope.
Notation "'(−⋅' y ')'" := (magma_mul_r_resp y) : magma_scope.

(** Left multiplication also respects its fixed factor, using pointwise
    equality of respectful maps rather than equality of function records. *)

(** 左乘也保持固定因子的相等，使用保相等映射的逐点相等，不比较函数记录。 *)

Global Instance magma_mul_l_proper {M : Magma}
  : Proper (carrier_equiv M ==> carrier_equiv (M →S M))
      (λ x : M, (x ⋅−)).
Proof.
  intros x y H z. apply (@magma_mul_proper _ (hasMagma M)); [exact H | reflexivity].
Qed.

(** Right multiplication respects its fixed factor pointwise. *)

(** 右乘逐点保持固定因子的相等。 *)

Global Instance magma_mul_r_proper {M : Magma}
  : Proper (carrier_equiv M ==> carrier_equiv (M →S M))
      (λ y : M, (−⋅ y)).
Proof.
  intros x y H z. apply (@magma_mul_proper _ (hasMagma M)); [reflexivity | exact H].
Qed.
