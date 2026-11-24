From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Algebra.

(** * Qualified access from another library

    [Require] loads the declarations. Reading metadata for a qualified
    name preserves the client's namespace. The constructor types check
    that the parent contributes its individual fields. *)

Minks.Inspect Algebra.Magma.
Minks.Inspect Algebra.HasMagma.
Minks.Inspect Algebra.HasMonoid.
Minks.Inspect Algebra.hasMagma.
Fail Minks.Inspect hasMagma.

Minks.Struct QualifiedChild
  extends Algebra.Magma.
Check @MakeQualifiedChild
  : ∀ (A : Type) (E : Algebra.HasEquiv A), @Algebra.HasMagma A E → QualifiedChild.
Check QualifiedChildToMagma : QualifiedChild → Algebra.Magma.

Minks.Struct ByFields
  extends Algebra.SetC
  with  Algebra.hasMagma : Algebra.HasMagma.
Minks.Struct Both
  extends QualifiedChild, ByFields.
Check @MakeBoth
  : ∀ (A : Type) (E : Algebra.HasEquiv A), @Algebra.HasMagma A E → Both.
Fail Check Magma.

Module OpenModule.
Minks.Struct First (A : Type) with ownOperation : Algebra.HasPoint [A].
Minks.Struct Second (A : Type) with OpenModule.ownOperation : Algebra.HasPoint [A].
Minks.Struct Same (A : Type) extends First A, Second A.
Check @MakeSame : ∀ A, Algebra.HasPoint A → Same A.
End OpenModule.

Module Public.
Export Algebra.
End Public.

Module Client.
Import Public.
Minks.Inspect hasMagma.
Minks.Struct FromImport
  extends SetC
  with  hasMagma : HasMagma.
Minks.Struct Rejoined
  extends FromImport, Algebra.Magma.
Check @MakeRejoined : ∀ (A : Type) (E : HasEquiv A), @HasMagma A E → Rejoined.
End Client.
Fail Check Magma.
