From Minks Require Import all.

Set Universe Polymorphism.

(** @lang both
    A documented component and its selected packed view. *)

Minks.Mixin HasExportPoint (A : Type)
  :=
  { export_point : A }.

(** @lang both
    The relative interface retains the same selected point. *)

Minks.Struct ExportPointed
  extends Type
  with hasExportPoint : HasExportPoint
  exports ExportPointOn [carrier].

Definition selected_point (P : ExportPointed)
  : P
  := export_point.

Example packed_point_computes (A : Type) (p : HasExportPoint A)
  : selected_point (MakeExportPointed A p) = @export_point A p.
Proof. reflexivity. Qed.
