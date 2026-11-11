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

(** The xor monoid, explicitly selected rather than globally registered. *)

(** 异或幺半群须显式选择，不全局注册。 *)

Program Definition BoolS_Monoid
  : Monoid BoolS
  :=
  {|monoid_unit := false
  ; monoid_mul := xorb
  |}.
Next Obligation. destruct x; reflexivity. Defined.
Next Obligation. destruct x; reflexivity. Defined.
Next Obligation. destruct x, y, z; reflexivity. Defined.

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
