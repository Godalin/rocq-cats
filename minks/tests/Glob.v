From Minks Require Import all.

Set Universe Polymorphism.

(** Authored fields retain their own source locations. *)

Minks.Mixin HasGlobValue (A : Type)
  :=
  { glob_value : A }.

Minks.Mixin HasGlobFlag
  :=
  { glob_flag : bool }.

(** Generated and aliased projections have declaration metadata even when
    their names do not occur as field identifiers in the source. *)

Minks.Struct GlobParent
  extends Type
  with  globPoint as chosenGlobPoint : HasGlobValue.

Minks.Struct GlobChild
  extends GlobParent
  with  childPoint : HasGlobValue [carrier]
  exports GlobOn [GlobParent].

Example inherited_glob_choice (P : GlobChild)
  : chosenGlobPoint (GlobChildToGlobParent P) = GlobChild_globPoint P
  := eq_refl.

Example relative_glob_choice (P : GlobChild)
  : GlobOn_childPoint (GlobChildToGlobOn P) = GlobChild_childPoint P
  := eq_refl.

(** A native parent adds a generated base and a generated carrier projection. *)

Record NativeGlob
  :=
  { run_glob : nat -> nat }.

Minks.Struct GlobNative
  extends NativeGlob
  with  globTag : HasGlobFlag.

Example native_glob_choice (P : NativeGlob) (F : HasGlobFlag)
  : GlobNativeToNativeGlob (MakeGlobNative P F) = P
  := eq_refl.
