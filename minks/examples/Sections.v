From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import Algebra.

(** * Section parameters

    Extend a law over a section carrier before and after a nested [End]. *)

(** The sort parent from the imported algebra hierarchy is the resolved base. *)

Minks.Struct ImportedSort
  extends Type.
Check ImportedSortToTypeCarrier : ImportedSort → Algebra.TypeCarrier.

Section Carrier.
Context {A : Type}.

Minks.Mixin HasChosen
  extends HasPoint A
  := { another_choice : A }.

(** The inner definition unfolds when the inner section closes. *)

Section AtElement.
Variable x : A.
Let y := x.

Minks.Mixin HasAtElement
  extends HasChosen
  := { value_at : point = y }.
End AtElement.

Minks.Inspect HasAtElement.
Minks.Mixin HasAgain (x : A)
  extends HasAtElement x
  := { selected_again : A }.
End Carrier.

Minks.Inspect HasAgain.
Check @HasAgain : ∀ (A : Type) (P : HasPoint A)
    (C : @HasChosen A P) (x : A), @HasAtElement A x P C → Type.

Minks.Mixin HasAfter (B : Type) (x : B)
  extends HasAgain (A := B) x
  := { after_choice : B }.

(** Only the label depends on [B]. The pointed setoid stays independent. *)

Section PointedFamily.
Variable B : Type.
Minks.Mixin HasLabel := { label : B }.
Minks.Struct LabelledPoint
  extends PointedSetC
  with  hasLabel : HasLabel
  exports LabelledOn [carrier].
End PointedFamily.
Minks.Inspect LabelledPoint.
Minks.Inspect LabelledOn.
Check @LabelledPointToPointedSetC : ∀ B : Type, LabelledPoint B → PointedSetC.
Check @LabelledPointOfPointedSetC
  : ∀ (B : Type) (P : PointedSetC), HasLabel B → LabelledPoint B.

(** Reuse the discharged export as a mixin parent. Its label and its
    pointed carrier have independent types. *)

Minks.Mixin HasMarkedLabel (B A : Type)
  extends LabelledOn B A
  := { marked_label : B }.

(** Explicit inputs distinguish section assumptions from stored fields. *)

Section ExplicitInput.
Context (B : Type).

Minks.Struct ChosenLabel
  extends PointedSetC
  with  labelWitness : HasLabel [B].

Fail Minks.Struct AmbiguousLabel
  extends PointedSetC
  with  B : HasPoint [carrier],
        labelWitness : HasLabel [B].

End ExplicitInput.

Check @ChosenLabelOfPointedSetC
  : ∀ (B : Type) (P : PointedSetC), HasLabel B → ChosenLabel B.

(** Specialize the parent at a differently named assumption. *)

Section InheritedFamily.
Variable D : Type.
Minks.Struct ExtendedLabel
  extends LabelledPoint D
  with  alternateLabel : HasLabel [D]
  exports AnotherLabel [LabelledPoint].
End InheritedFamily.

Check @ExtendedLabelOfAnotherLabel
  : ∀ D (P : LabelledPoint D), AnotherLabel D P → ExtendedLabel D.

Check @ExtendedLabelOfLabelledPoint
  : ∀ D (P : LabelledPoint D), HasLabel D → ExtendedLabel D.

(** The direct and transitive parent views retain that specialization. *)

Section FurtherFamily.
Variable T : Type.
Minks.Struct FurtherLabel
  extends ExtendedLabel T.

Fail Minks.Struct MissingLabelParameter
  extends ExtendedLabel.

Variable U : Type.
Fail Minks.Struct ConflictingLabels
  extends ExtendedLabel T, LabelledPoint U.
End FurtherFamily.

Check @FurtherLabelToLabelledPoint
  : ∀ T : Type, FurtherLabel T → LabelledPoint T.

(** A discharged virtual mixin assembles its fields at the chosen input. *)

Section RelativeFamily.
Context (D : Type).
Minks.Struct LabelFromExport
  extends PointedSetC
  with  chosen : LabelledOn [D, carrier].
End RelativeFamily.

Check @LabelFromExport_chosen
  : ∀ D (P : LabelFromExport D), LabelledOn D P.

(** Ordinary section assumptions may also have a registered witness type.
    An explicit input fixes the witness used by each later argument. *)

Section FixedWitnesses.
Context (A : Type) (E : HasEquiv A) (M : @HasMagma A E).

Minks.Struct AssocWitness
  with  law : IsSemigroup [A, E, M].

End FixedWitnesses.

Minks.Inspect AssocWitness.

Check @AssocWitness_law
  : ∀ A (E : HasEquiv A) (M : @HasMagma A E),
    AssocWitness A E M → @IsSemigroup A E M.

(** Extending the discharged distributivity law takes both ordinary
    operation arguments and introduces exactly one inherited witness. *)

Minks.Mixin IsIdempotentDistributive (A : Type) (E : HasEquiv A)
    (addOp mulOp : @HasMagma A E)
  extends IsDistributive A E addOp mulOp
  := { add_idempotent : ∀ x, @mul _ _ addOp x x ≈ x }.

Check @IsIdempotentDistributive
  : ∀ (A : Type) (E : HasEquiv A) (addOp mulOp : @HasMagma A E),
    IsDistributive A E addOp mulOp → Type.

Fail Minks.Mixin MissingOrdinaryOperation (A : Type) (E : HasEquiv A)
    (op : @HasMagma A E)
  extends IsDistributive A E op
  := { missing_operation : True }.

(** A packed base can itself have a section parameter. Its carrier and
    equivalence projections take both the parameter and the packed value. *)

Section LabelledMultiplication.
Variable B : Type.

Minks.Struct LabelledMagma
  extends LabelledPoint B
  with  hasMagma : HasMagma [carrier, hasEquiv]
  exports MagmaOnLabelled [LabelledPoint].
End LabelledMultiplication.

Minks.Mixin IsLabelledSemigroup (T : Type) (S : LabelledPoint T)
  extends MagmaOnLabelled T S
  := { labelled_assoc : ∀ x y z : S, (x * y) * z ≈ x * (y * z) }.

Section AtLabelledPoint.
Context (T : Type) (S : LabelledPoint T).

Minks.Struct AtLabel
  with  chosen : MagmaOnLabelled [T, S].
End AtLabelledPoint.

Example labelled_op_computes (T : Type) (S : LabelledPoint T)
    (op : @HasMagma S (LabelledPoint_hasEquiv T S))
  : MagmaOnLabelled_hasMagma T (AtLabel_chosen T S (MakeAtLabel T S op)) = op
  := eq_refl.
