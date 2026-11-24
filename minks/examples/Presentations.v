From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import
  Algebra
  Sharing.

Set Universe Polymorphism.

(** * A monoid interface and its constituent mixins

    Compare the two declarations on arbitrary inputs. Reading the whole
    monoid interface checks the selected laws as well as the operations. *)

Module ViaExport.
Minks.Mixin Marked (A : Type)
  extends HasMonoid A
  := { mark : A }.

Minks.Struct Packed
  extends Type
  with  : HasMonoid.
End ViaExport.

Module ByParts.
Minks.Mixin Marked (A : Type)
  extends IsSemigroup A, IsUnitAt A
  := { mark : A }.

Minks.Struct Packed
  extends Type
  with  hasEquiv : HasEquiv,
        hasMagma : HasMagma,
        isSemigroup : IsSemigroup,
        hasPoint : HasPoint,
        isUnitAt : IsUnitAt.
End ByParts.

Module UnitFirst.
Minks.Mixin Marked (A : Type)
  extends IsUnitAt A, IsSemigroup A
  := { mark : A }.
End UnitFirst.

(** Compare the full mixin parameter types at the same universe instance.
    Conversion also unfolds the local definition of the assembled export. *)

Example same_mixin_signature@{u e +}
  : ltac:(let t := type of @ViaExport.Marked@{u e} in exact t)
    = ltac:(let t := type of @ByParts.Marked@{u e} in exact t)
  := eq_refl.

(** Compare the constructor types after replacing their respective record
    results with [unit]. The dependent types of all fields stay intact. *)

Ltac packed_fields constructor result :=
  let t := type of constructor in
  let abstracted := eval pattern result in t in
  lazymatch abstracted with
  | ?fields _ => exact (fields unit)
  end.

Example same_packed_signature@{u v e +}
  : ltac:(packed_fields @ViaExport.MakePacked@{u v e} ViaExport.Packed@{u v e})
    = ltac:(packed_fields @ByParts.MakePacked@{u v e} ByParts.Packed@{u v e})
  := eq_refl.

(** Both constructors take the same arguments in the same positions.
    Reversing the parents puts the point and its laws before associativity. *)

Section MonoidInputs.
Context (A : Type) (E : HasEquiv A) (M : @HasMagma A E)
  (S : @IsSemigroup A E M) (P : HasPoint A) (U : @IsUnitAt A E M P).

Example same_mark (x : A)
  : ViaExport.mark (Marked := ViaExport.Build_Marked A E M S P U x)
    = ByParts.mark (Marked := ByParts.Build_Marked A E M S P U x)
  := eq_refl.

Check @UnitFirst.Marked A E M P U S : Type.
Fail Check @UnitFirst.Marked A E M S P U.

Example same_monoid_fields
  : let r := ByParts.MakePacked A E M S P U in
    let l := ViaExport.MakePacked A E M S P U in
    MakeHasMonoid A (ViaExport.Packed_hasEquiv l) (ViaExport.Packed_hasMagma l)
      (ViaExport.Packed_isSemigroup l) (ViaExport.Packed_hasPoint l)
      (ViaExport.Packed_isUnitAt l)
    = MakeHasMonoid (ByParts.Packed_carrier r)
        (ByParts.Packed_hasEquiv r) (ByParts.Packed_hasMagma r)
        (ByParts.Packed_isSemigroup r) (ByParts.Packed_hasPoint r)
        (ByParts.Packed_isUnitAt r)
  := eq_refl.
End MonoidInputs.

(** * A specified magma

    The single remaining component of [PointOnPackedMagma M] is the
    ordinary mixin [HasPoint] on the carrier projected from [M]. *)

Module OverMagma.
Section FixedMagma.
Context (M : Magma).
Let A := Magma_carrier M.

Minks.Mixin Marked
  extends PointOnPackedMagma M
  := { mark : A }.
End FixedMagma.
End OverMagma.

Module OnCarrier.
Section FixedMagma.
Context (M : Magma).
Let A := Magma_carrier M.
Let E := Magma_hasEquiv M.
Let op := Magma_hasMagma M.

Minks.Mixin Marked
  extends HasPoint A
  := { mark : A }.

Minks.Struct Packed
  with  assocAt : IsSemigroup [A, E, op],
        pointAt : HasPoint [A],
        unitAt : IsUnitAt [A, E, op, pointAt].
End FixedMagma.
End OnCarrier.

Example same_relative_mixin_signature@{u e +}
  : ltac:(let t := type of @OverMagma.Marked@{u e} in exact t)
    = ltac:(let t := type of @OnCarrier.Marked@{u e} in exact t)
  := eq_refl.

Example same_mark_over_magma (M : Magma) (P : HasPoint M) (x : M)
  : OverMagma.mark M (Marked := OverMagma.Build_Marked M P x)
    = OnCarrier.mark M (Marked := OnCarrier.Build_Marked M P x)
  := eq_refl.

Example same_relative_fields (M : Magma) (S : IsSemigroup M)
    (P : HasPoint M) (U : IsUnitAt M (hasPoint := P))
  : let r := OnCarrier.MakePacked M S P U in
    let l := MakeMonoidOnMagma M S P U in
    MakeIsMonoid M (MonoidOnMagma_assocAt M l) (MonoidOnMagma_pointAt M l)
      (MonoidOnMagma_unitAt M l)
    = MakeIsMonoid M (OnCarrier.Packed_assocAt M r)
        (OnCarrier.Packed_pointAt M r) (OnCarrier.Packed_unitAt M r)
  := eq_refl.
