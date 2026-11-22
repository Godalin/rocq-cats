From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import Algebra.

(** * Universe instances of mixins

    Infer levels at declaration time and constrain them explicitly in
    clients. The two branches share the chosen equivalence and select
    elements at independent levels. *)

Set Universe Polymorphism.

Minks.Mixin HasLeftValue (A X : Type)
  extends HasEquiv A
  :=
  { left_value : X }.

Minks.Mixin HasRightValue (A Y : Type)
  extends HasEquiv A
  :=
  { right_value : Y }.

Minks.Mixin HasTwoValues (A X Y : Type)
  extends HasLeftValue A X, HasRightValue A Y
  :=
  { paired_value : (X * Y)%type := (left_value, right_value) }.

(** The inferred carrier, witness, and branch levels can be strictly
    separated in either direction. The application uses the inferred
    positional order of this declaration. *)

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

Minks.Mixin HasNamedValues@{u e x y}
    (A : Type@{u}) (X : Type@{x}) (Y : Type@{y})
  extends HasLeftValue@{u e x} A X, HasRightValue@{u e y} A Y
  :=
  { named_left : X
  ; named_right : Y
  }.

(** The shared equivalence cannot take two explicitly different levels. *)

Fail Minks.Mixin ConflictingLevels@{u e p x y | e < p}
    (A : Type@{u}) (X : Type@{x}) (Y : Type@{y})
  extends HasLeftValue@{u e x} A X, HasRightValue@{u p y} A Y
  :=
  { conflicting_left : X
  ; conflicting_right : Y
  }.

(** An open universe declaration allows a fresh level for the new parameter. *)

Minks.Mixin HasOpenLevels@{u e +} (A : Type@{u}) (X : Type)
  extends HasEquiv@{u e} A
  :=
  { open_value : X }.

Fail Minks.Mixin HasClosedLevels@{u e} (A : Type@{u}) (X : Type)
  extends HasEquiv@{u e} A
  :=
  { closed_value : X }.

(** An explicit parent instance carries the parent's strict constraint. *)

Minks.Mixin HasLargeValue@{u e x | u < x} (A : Type@{u}) (X : Type@{x})
  extends HasEquiv@{u e} A
  :=
  { large_value : X }.

Minks.Mixin InheritsLargeValue@{u e x | u < x} (A : Type@{u}) (X : Type@{x})
  extends HasLargeValue@{u e x} A X
  :=
  { inherited_large_value : X := large_value }.

Fail Minks.Mixin ReversedLargeValue@{u e x | x < u} (A : Type@{u}) (X : Type@{x})
  extends HasLargeValue@{u e x} A X
  :=
  { reversed_large_value : X := large_value }.

(** ** Universe order with an existing carrier record

    Keep the two levels of a native carrier record in their declared order.
    A new family on that carrier adds its own level after those two. *)

Record FixedCarrier@{u e}
  :=
  { fixed_carrier :> Type@{u}
  ; fixed_equiv : fixed_carrier → fixed_carrier → Type@{e}
  }.

(** A sort parent and a native record request different concrete coercions.
    Neither ordering can merge the two types under the same field key. *)

Fail Minks.Struct ConflictingNativeCarrier
  extends Type, FixedCarrier.

Fail Minks.Struct ConflictingSortCarrier
  extends FixedCarrier, Type.

Record NativeMap
  :=
  { run_native_map :> bool → bool }.

Minks.Struct PackedMap
  extends NativeMap.

Example packed_map_computes (f : NativeMap) (x : bool)
  : (MakePackedMap f) x = f x
  := eq_refl.

Minks.Mixin HasFixedPoint (S : FixedCarrier)
  :=
  { fixed_point : S }.

Minks.Mixin HasFixedFamily@{u e i} (S : FixedCarrier@{u e})
  :=
  { fixed_family : S → Type@{i} }.

Minks.Struct FixedPointed
  extends FixedCarrier
  with  hasFixedPoint : HasFixedPoint.

Minks.Struct FixedPointFamily
  extends FixedCarrier, FixedPointed
  with  hasFixedFamily : HasFixedFamily
  exports HasFixedFamilyChoice [hasFixedPoint],
          HasFixedFamilyOnPointed [FixedPointed].

Definition fixed_carrier_levels@{u e i | u < e, e < i}
    (S : FixedPointFamily@{u e i})
  : FixedCarrier@{u e}
  := FixedPointFamilyToFixedCarrier S.

Definition fixed_parent_levels@{u e i | e < u, u < i}
    (S : FixedPointFamily@{u e i})
  : FixedPointed@{u e}
  := FixedPointFamilyToFixedPointed S.

(** The relative interface preserves the independent family level. *)

Definition fixed_export_levels@{u e i | i < u, u < e}
    (S : FixedPointFamily@{u e i})
  : HasFixedFamilyChoice@{u e i}
      (FixedPointFamilyToFixedCarrier S) (FixedPointFamily_hasFixedPoint S)
  := FixedPointFamilyToHasFixedFamilyChoice S.

(** A packed base preserves its carrier levels and the separate family level. *)

Definition packed_export_levels@{u e i | i < u, u < e}
    (S : FixedPointFamily@{u e i})
  : HasFixedFamilyOnPointed@{u e i} (FixedPointFamilyToFixedPointed S)
  := FixedPointFamilyToHasFixedFamilyOnPointed S.

(** Inheriting an exported interface preserves the specified family level.
    The projection reduces to the family witness supplied to the mixin. *)

Minks.Mixin HasFixedFamilyMember@{u e i | i < u, u < e}
    (S : FixedCarrier@{u e}) (P : HasFixedPoint S)
  extends HasFixedFamilyChoice@{u e i} S P
  :=
  { fixed_family_member :
      @fixed_family S
        (@HasFixedFamilyChoice_hasFixedFamily S P hasFixedFamilyChoice)
        (@fixed_point S P)
  }.

Definition fixed_family_member_levels@{u e i | i < u, u < e}
    (S : FixedCarrier@{u e}) (P : HasFixedPoint S) (F : HasFixedFamily@{u e i} S)
    (M : @HasFixedFamilyMember@{u e i} S F P)
  : @fixed_family S F (@fixed_point S P)
  := @fixed_family_member S F P M.

(** A mixin that identifies two carrier levels induces one parameter. *)

Minks.Mixin HasSameLevelPoint@{u} (S : FixedCarrier@{u u})
  :=
  { same_level_point : S }.

Minks.Struct FixedSameLevel
  extends FixedCarrier
  with  hasSameLevelPoint : HasSameLevelPoint.

Definition fixed_shared_level@{u} (S : FixedSameLevel@{u})
  : FixedCarrier@{u u}
  := FixedSameLevelToFixedCarrier S.

(** With universe polymorphism disabled, inferred levels are fixed. *)

Unset Universe Polymorphism.

Minks.Mixin HasFixedLevels (A : Type)
  :=
  { fixed_value : A }.

Check HasFixedLevels.
Fail Check HasFixedLevels@{Set}.
