From Stdlib Require Import
  Bool.
From Cats Require Import
  Algebra.Group.Core.

Local Open Scope algebra_scope.

(** * The Cyclic Group of Order Two

    Boolean xor has unit [false], and every element is its own inverse.
    Native boolean equality is the specified equality of this concrete set. *)

(** * 二阶循环群

    布尔异或以 [false] 为单位，每个元素自逆；此具体集合指定布尔原生相等作为
    其相等关系。 *)

Program Definition BoolS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv := eq
  ; carrier_setoid := eq_equivalence
  |}.

(** The xor magma, explicitly selected rather than globally registered. *)

(** 异或原群须显式选择，不全局注册。 *)

Program Definition BoolS_Magma
  : Magma
  :=
  {|MagmaToSetC := BoolS
  ; hasMagma :=
      {|mul := xorb
      ; mul_proper := _
      |}
  |}.

(** Associativity extends that same operation to a semigroup. *)

(** 结合律将同一运算扩展为半群。 *)

Program Definition BoolS_Semigroup
  : Semigroup
  :=
  {|SemigroupToMagma := BoolS_Magma
  ; isSemigroup := {|mul_assoc := _|}
  |}.
Next Obligation. destruct x, y, z; reflexivity. Defined.

(** The xor monoid adds its unit to the selected semigroup. *)

(** 异或幺半群为选定半群增加单位元。 *)

Program Definition BoolS_HasMonoid
  : HasMonoid BoolS_Semigroup
  :=
  {|mul_unit := false
  ; isMonoid :=
      {|mul_unit_l := _
      ; mul_unit_r := _
      |}
  |}.
Next Obligation. destruct x; reflexivity. Defined.
Next Obligation. destruct x; reflexivity. Defined.

(** The existing monoid view retains that same semigroup and extension. *)

(** 现有幺半群视图保留同一半群及扩充。 *)

Definition BoolS_Monoid
  : Monoid
  := MonoidOfSemigroup BoolS_Semigroup BoolS_HasMonoid.

(** Inversion is the identity function, extending the same selected monoid. *)

(** 取逆为恒等函数，扩展同一个选定幺半群。 *)

Program Definition BoolS_HasGroup
  : HasGroup BoolS_Monoid
  :=
  {|inv x := x
  ; isGroup :=
      {|mul_inv_l := _
      ; mul_inv_r := _
      |}
  |}.
Next Obligation. destruct x; reflexivity. Defined.
Next Obligation. destruct x; reflexivity. Defined.

(** Retain the same monoid and its explicitly chosen identity inverse. *)

(** 保留同一幺半群及其显式选定的恒等逆。 *)

Definition BoolS_Group
  : Group
  := GroupOfMonoid BoolS_Monoid BoolS_HasGroup.
