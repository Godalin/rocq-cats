From Stdlib Require Import
  Bool.
From Cats Require Import
  Algebra.Group.Core.

Local Open Scope monoid_scope.

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
  : Magma BoolS
  :=
  {|magma_mul := xorb
  |}.

(** Associativity extends that same operation to a semigroup. *)

(** 结合律将同一运算扩展为半群。 *)

Program Definition BoolS_Semigroup
  : Semigroup BoolS
  :=
  {|SemigroupM := BoolS_Magma
  |}.
Next Obligation. destruct x, y, z; reflexivity. Defined.

(** The xor monoid adds its unit to the selected semigroup. *)

(** 异或幺半群为选定半群增加单位元。 *)

Program Definition BoolS_HasMonoid
  : HasMonoid BoolS_Semigroup
  :=
  {|monoid_chosen_unit := false
  ; isMonoid :=
      {|monoid_unit_left := _
      ; monoid_unit_right := _
      |}
  |}.
Next Obligation. destruct x; reflexivity. Defined.
Next Obligation. destruct x; reflexivity. Defined.

(** The existing monoid view retains that same semigroup and extension. *)

(** 现有幺半群视图保留同一半群及扩充。 *)

Definition BoolS_Monoid
  : Monoid BoolS
  := MonoidFromExtension BoolS_Semigroup BoolS_HasMonoid.

(** Inversion is the identity function, extending the same selected monoid. *)

(** 取逆为恒等函数，扩展同一个选定幺半群。 *)

Program Definition BoolS_Group
  : Group BoolS
  :=
  {|GroupM := BoolS_Monoid
  ; group_inv x := x
  |}.
Next Obligation. destruct x; reflexivity. Defined.
Next Obligation. destruct x; reflexivity. Defined.
