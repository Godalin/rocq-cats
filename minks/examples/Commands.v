From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import Algebra.

(** * Checks for the public commands

    Import a hierarchy from another file, extend one of its records, and
    verify that an incompatible component fails before declaring a record. *)

(** * 公开命令检查

    导入另一文件声明的层级，扩展其中的记录，并验证组件冲突会在声明记录前被拒绝。 *)

Minks.Struct ClientMonoid extends Algebra.Monoid.
Check ClientMonoidToMonoid : ClientMonoid → Algebra.Monoid.

(** The generated ancestor view agrees with projection through the parent. *)

(** 生成的祖先视图与经过父结构的投影一致。 *)

Example client_setoid_view (M : ClientMonoid)
  : ClientMonoidToSetC M = MonoidToSetC (ClientMonoidToMonoid M)
  := eq_refl.

(** The imported record's projection instances are available to clients. *)

(** 导入记录后，调用者可以搜索该记录的投影实例。 *)

Definition imported_assoc (M : Algebra.Monoid) (x y z : M)
  : equiv (mul (mul x y) z) (mul x (mul y z))
  := mul_assoc x y z.

(** Reject a shared multiplication with incompatible selected dependencies. *)

(** 共享乘法的选定依赖若不一致，生成器应拒绝合并。 *)

Minks.Struct OtherMagma extends SetC
  with  hasOtherEquiv : HasEquiv [carrier],
        hasMagma : HasMagma [carrier, hasOtherEquiv].
Fail Minks.Struct ConflictingMagma extends Magma, OtherMagma.
Fail Check ConflictingMagma.

(** Only Minks declarations supply component metadata. *)

(** 组件元数据来自 Minks 声明。 *)

Class OrdinaryChoice (A : Type)
  :=
  { ordinary_choice : A }.

Fail Elpi minks.mixin OrdinaryChoice.
Fail Minks.Struct UnregisteredChoice
  with  hasChoice : OrdinaryChoice.
Fail Minks.Struct ExplicitUnregisteredChoice
  with  hasChoice : OrdinaryChoice [carrier].
Fail Check ExplicitUnregisteredChoice.

Fail Minks.Struct Incomplete extends.
Fail Minks.Inspect bool.

(** Extend independent branches on one selected point and one equivalence. *)

(** 在同一个选定点和同一份相等关系上扩展两条独立分支。 *)

Set Universe Polymorphism.

Minks.Mixin IsNamedPoint (x : A) extends HasEquiv
  :=
  { named_point_refl : equiv x x }.

Minks.Mixin IsLeftPoint (y : A) extends HasPoint, IsNamedPoint
  :=
  { left_point_refl : equiv y y }.

Minks.Mixin IsRightPoint (y : A) extends IsNamedPoint
  :=
  { right_point_refl : equiv y y }.

Minks.Mixin IsBothPoints extends IsLeftPoint, IsRightPoint
  :=
  { both_points_refl : equiv x x }.

(** Check the order of the shared and branch-specific parameters. *)

(** 检查共享参数及各分支参数的顺序。 *)

Check @IsBothPoints
  : ∀ (A : Type) (E : HasEquiv A)
      (x : A) (N : @IsNamedPoint A E x) (P : HasPoint A)
      (y : A) (L : @IsLeftPoint A P E x N y)
      (z : A) (R : @IsRightPoint A E x N z), Type.

(** Keep the braces on the carrier and the index through two extensions. *)

(** 经过两次扩展后，载体和索引仍保持花括号指定的隐式属性。 *)

Minks.Mixin HasSeed {A : Type}
  :=
  { seed : A }.

Minks.Mixin IsSeed {x : A} extends HasSeed
  :=
  { seed_eq : seed = x }.

Minks.Mixin IsSeedAt (y : A) extends IsSeed
  :=
  { seed_at : x = y }.

Example inherited_implicit_parameters {A : Type} {x : A}
    (S : @HasSeed A) (I : @IsSeed A S x)
    (y : A) (P : IsSeedAt y)
  : @IsSeedAt A S x I y
  := P.

(** Discover a proper structural view once both records exist. *)

(** 两个记录都已声明时发现严格子结构转换。 *)

Minks.Struct EarlierPointed
  with  chosenPoint : HasPoint,
        chosenEquiv : HasEquiv.

Minks.Struct LaterPoint
  with  chosenPoint : HasPoint.

Example earlier_view_preserves_point (S : EarlierPointed)
  : LaterPoint_chosenPoint (EarlierPointedToLaterPoint S)
    = EarlierPointed_chosenPoint S
  := eq_refl.

Minks.Struct LaterPointed
  with  chosenPoint : HasPoint,
        secondEquiv : HasEquiv.

Example later_view_preserves_point (S : LaterPointed)
  : LaterPoint_chosenPoint (LaterPointedToLaterPoint S)
    = LaterPointed_chosenPoint S
  := eq_refl.

Fail Check LaterPointToEarlierPointed.
