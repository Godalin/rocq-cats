(** * Public Minks commands

    Import this module to declare and inspect mixins and structures. *)

(** * Minks 公开命令

    导入此模块即可声明和查看 Mixin 与结构。 *)

From elpi Require Import elpi.
From Minks Require Import
  Mixin
  Struct.

Elpi Export minks.struct As Minks.Struct.
Elpi Export minks.inspect As Minks.Inspect.
