From Cats Require Export
  Algebra.Semigroup.Core.

Declare Scope monoid_scope.
Delimit Scope monoid_scope with monoid.
Infix "⋅" := magma_mul (at level 40, left associativity) : monoid_scope.
Local Open Scope monoid_scope.

(** * Monoids on Sets

    A monoid adds a unit to one selected semigroup. The inherited magma
    stores multiplication once, and all laws use the specified Type-valued
    setoid equality rather than native equality. *)

(** * 广集上的幺半群

    幺半群为一个选定半群增加单位元。继承的原群只保存一次乘法，所有定律
    使用指定的 Type 值广集相等，不要求原生相等。 *)

Class Monoid (M : SetC)
  :=
  (** The semigroup is the unique parent; its magma recovers the same
      named setoid. [SG] distinguishes this parent from a setoid view. *)

  (** 半群是唯一父结构，其原群恢复同一具名广集；[SG] 区分半群父结构与
      广集视图。 *)

  { MonoidSG :> Semigroup M

  (** Select a two-sided unit for the inherited multiplication. *)

  (** 为继承的乘法选取双侧单位元。 *)

  ; monoid_unit : M
  ; monoid_unit_l x : monoid_unit ⋅ x ≈S x
  ; monoid_unit_r x : x ⋅ monoid_unit ≈S x
  }.

Arguments MonoidSG {_} _.

(** Register the same parent for inherited instance search. *)

(** 将同一父结构注册到继承实例搜索。 *)

#[export] Existing Instance MonoidSG.

Notation "1" := monoid_unit : monoid_scope.

(** A left and a right inverse of the same element agree. This elementary
    argument supplies all later coherence of selected group inverses. *)

(** 同一元素的左逆与右逆相等；此基本论证提供后续选定群逆的全部相干性。 *)

Lemma monoid_inverse_unique {M : SetC} `{HM : !Monoid M}
    (x y z : M) (Hy : y ⋅ x ≈S 1) (Hz : x ⋅ z ≈S 1)
  : y ≈S z.
Proof.
  transitivity (y ⋅ (x ⋅ z)).
  - rewrite Hz, monoid_unit_r. reflexivity.
  - rewrite <- semigroup_assoc, Hy, monoid_unit_l. reflexivity.
Qed.
