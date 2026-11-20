From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import Algebra.

(** * Universe instances of mixins

    Infer levels at declaration time and constrain them explicitly in
    clients. The two branches share the chosen equivalence and select
    elements at independent levels. *)

(** * Mixin 的宇宙实例

    在声明处推断宇宙，在调用处显式施加约束。两条分支共享选定的相等关系，
    各自在独立的宇宙选取元素。 *)

Set Universe Polymorphism.

Minks.Mixin HasLeftValue (X : Type) extends HasEquiv
  :=
  { left_value : X }.

Minks.Mixin HasRightValue (Y : Type) extends HasEquiv
  :=
  { right_value : Y }.

Minks.Mixin HasTwoValues extends HasLeftValue, HasRightValue
  :=
  { paired_value : (X * Y)%type := (left_value, right_value) }.

(** The inferred carrier, witness, and branch levels can be strictly
    separated in either direction. The application uses the inferred
    positional order of this declaration. *)

(** 推断得到的载体、见证及分支宇宙可以按两种严格方向分离。
    应用按该声明推断出的宇宙位置传入参数。 *)

Definition left_level_smaller@{u e x y | u < e, e < x, x < y}
    (A : Type@{u}) (E : HasEquiv@{u e} A)
    (X : Type@{x}) (L : @HasLeftValue@{u e x} A E X)
    (Y : Type@{y}) (R : @HasRightValue@{u e y} A E Y)
  : Prop
  := @HasTwoValues@{u x y e} A E X L Y R.

Definition right_level_smaller@{u e x y | y < x, x < e, e < u}
    (A : Type@{u}) (E : HasEquiv@{u e} A)
    (X : Type@{x}) (L : @HasLeftValue@{u e x} A E X)
    (Y : Type@{y}) (R : @HasRightValue@{u e y} A E Y)
  : Prop
  := @HasTwoValues@{u x y e} A E X L Y R.

(** Name an inherited parameter universe and keep a single instance
    of the equivalence in both branches. *)

(** 为继承的参数宇宙命名，并让两条分支共用同一个相等关系实例。 *)

Minks.Mixin HasNamedValues@{u e x y}
  extends HasLeftValue@{u e x}, HasRightValue@{u e y}
  :=
  { named_left : X
  ; named_right : Y
  }.

(** The shared equivalence cannot take two explicitly different levels. *)

(** 共享的相等见证不能同时取两个显式不同的宇宙。 *)

Fail Minks.Mixin ConflictingLevels@{u e p x y | e < p}
  extends HasLeftValue@{u e x}, HasRightValue@{u p y}
  :=
  { conflicting_left : X
  ; conflicting_right : Y
  }.

(** An open universe declaration allows a fresh level for the new parameter. *)

(** 开放的宇宙声明允许新参数引入新的层级。 *)

Minks.Mixin HasOpenLevels@{u e +} (X : Type) extends HasEquiv@{u e}
  :=
  { open_value : X }.

Fail Minks.Mixin HasClosedLevels@{u e} (X : Type) extends HasEquiv@{u e}
  :=
  { closed_value : X }.

(** An explicit parent instance carries the parent's strict constraint. *)

(** 显式实例化父级时保留其严格宇宙约束。 *)

Minks.Mixin HasLargeValue@{u e x | u < x} (X : Type@{x})
  extends HasEquiv@{u e}
  :=
  { large_value : X }.

Minks.Mixin InheritsLargeValue@{u e x | u < x}
  extends HasLargeValue@{u e x}
  :=
  { inherited_large_value : X := large_value }.

Fail Minks.Mixin ReversedLargeValue@{u e x | x < u}
  extends HasLargeValue@{u e x}
  :=
  { reversed_large_value : X := large_value }.

(** With universe polymorphism disabled, inferred levels are fixed. *)

(** 关闭宇宙多态时，推断出的层级固定在该声明中。 *)

Unset Universe Polymorphism.

Minks.Mixin HasFixedLevels (A : Type)
  :=
  { fixed_value : A }.

Check HasFixedLevels.
Fail Check HasFixedLevels@{Set}.
