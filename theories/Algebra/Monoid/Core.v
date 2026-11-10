From Cats.Set Require Export
  Morphism.

(** * Monoids on Sets

    The underlying set carries its specified Type-valued equality. Neither
    associativity nor the unit equations require native equality. *)

(** * 广集上的幺半群

    底层集合带指定的 Type 值相等，结合律与单位方程均不要求原生相等。 *)

Class Monoid (M : SetC)
  :=
  (** The underlying setoid is computed from the named parameter, without
      storing another carrier or choosing its algebraic structure. *)

  (** 底层广集由具名参数计算得到，不另存载体，也不自动选取其代数结构。 *)

  { MonoidS :> SetC := M
  ; monoid_unit : M
  ; monoid_mul : M → M → M
  ; monoid_mul_proper
    :: Proper (carrier_equiv M ==> carrier_equiv M ==> carrier_equiv M)
        monoid_mul
  ; monoid_unit_l x : monoid_mul monoid_unit x ≈S x
  ; monoid_unit_r x : monoid_mul x monoid_unit ≈S x
  ; monoid_assoc x y z
    : monoid_mul (monoid_mul x y) z ≈S monoid_mul x (monoid_mul y z)
  }.

Arguments MonoidS {_} _.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with monoid.
Notation "1" := monoid_unit : monoid_scope.
Infix "⋅" := monoid_mul (at level 40, left associativity) : monoid_scope.
Local Open Scope monoid_scope.

(** A left and a right inverse of the same element agree. This elementary
    argument supplies all later coherence of selected group inverses. *)

(** 同一元素的左逆与右逆相等；此基本论证提供后续选定群逆的全部相干性。 *)

Lemma monoid_inverse_unique {M : SetC} `{HM : !Monoid M}
    (x y z : M) (Hy : y ⋅ x ≈S 1) (Hz : x ⋅ z ≈S 1)
  : y ≈S z.
Proof.
  transitivity (y ⋅ (x ⋅ z)).
  - rewrite Hz, monoid_unit_r. reflexivity.
  - rewrite <- monoid_assoc, Hy, monoid_unit_l. reflexivity.
Qed.

(** Left multiplication is a respectful map of the underlying set. *)

(** 左乘是底层广集的保相等映射。 *)

Program Definition monoid_mul_l_resp {M : SetC} `{HM : !Monoid M} (x : M)
  : M →r M
  :=
  {|func y := x ⋅ y
  |}.
Next Obligation.
  intros y z H. apply monoid_mul_proper; [reflexivity | exact H].
Defined.

(** Right multiplication is also respectful. *)

(** 右乘同样保持指定相等。 *)

Program Definition monoid_mul_r_resp {M : SetC} `{HM : !Monoid M} (y : M)
  : M →r M
  :=
  {|func x := x ⋅ y
  |}.
Next Obligation.
  intros x z H. apply monoid_mul_proper; [exact H | reflexivity].
Defined.
