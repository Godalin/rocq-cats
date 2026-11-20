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

Fail Minks.Struct Incomplete extends.
Fail Minks.Inspect bool.
