From Cats Require Export
  Algebra.Semigroup.Core.

Local Open Scope algebra_scope.

(** * Monoids on Sets

    A monoid adds a unit to one selected semigroup. The inherited magma
    stores multiplication once, and all laws use the specified Type-valued
    setoid equality rather than native equality. *)

(** * 广集上的幺半群

    幺半群为一个选定半群增加单位元。继承的原群只保存一次乘法，所有定律
    使用指定的 Type 值广集相等，不要求原生相等。 *)

(** A specified element is a two-sided unit for the selected multiplication. *)

(** 指定元素是选定乘法的双侧单位元。 *)

Minks.Mixin IsUnit (S : SetC) (e : S)
  extends HasMagma S
  :=
  { mul_unit_l x : mul e x ≈S x
  ; mul_unit_r x : mul x e ≈S x
  }.

(** Choose a unit and retain its Type-valued laws on that multiplication. *)

(** 在这份乘法上选取单位元，并保留 Type 值定律。 *)

Minks.Mixin HasUnit (S : SetC)
  extends HasMagma S
  :=
  { mul_unit : S
  ; isUnit :: @IsUnit S mul_unit hasMagma
  }.

Arguments mul_unit_l {_ _ _ _} x.
Arguments mul_unit_r {_ _ _ _} x.

(** Store multiplication, associativity and a unit on one setoid. *)

(** 在一个广集上平铺保存乘法、结合律和单位元。 *)

Minks.Struct Monoid@{u p l}
  extends Semigroup@{u p l}
  with  hasUnit as hasUnit : HasUnit.

Notation "1" := (@mul_unit _ _ (hasUnit _))
  : algebra_scope.

(** Any two specified units of the same selected semigroup agree in its
    setoid equality. Their records and native carrier values need not agree. *)

(** 同一选定半群的任意两个指定单位元在其广集相等下相等，无须记录或载体值
    的原生相等。 *)

Lemma units_equiv {S : SetC} `{M : !HasMagma S} {e f : S}
    `{He : !@IsUnit S e M} `{Hf : !@IsUnit S f M}
  : e ≈S f.
Proof.
  transitivity (mul e f).
  - symmetry. rewrite mul_unit_r. reflexivity.
  - rewrite mul_unit_l. reflexivity.
Qed.

(** A left and a right inverse agree on the chosen monoid. *)

(** 在选定幺半群中左逆与右逆相等。 *)

Lemma mul_inv_unique {M : Monoid}
    (x y z : M)
    (Hy : y ⋅ x ≈S 1) (Hz : x ⋅ z ≈S 1)
  : y ≈S z.
Proof.
  transitivity (y ⋅ (x ⋅ z)).
  - rewrite Hz. symmetry.
    rewrite mul_unit_r. reflexivity.
  - rewrite <- mul_assoc, Hy.
    rewrite mul_unit_l. reflexivity.
Qed.
