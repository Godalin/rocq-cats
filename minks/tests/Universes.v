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
    (X : Type@{x}) (L : @HasLeftValue@{u x e} A X E)
    (Y : Type@{y}) (R : @HasRightValue@{u y e} A Y E)
  : Prop
  := @HasTwoValues@{u x y e} A X Y E L R.

Definition right_level_smaller@{u e x y | y < x, x < e, e < u}
    (A : Type@{u}) (E : HasEquiv@{u e} A)
    (X : Type@{x}) (L : @HasLeftValue@{u x e} A X E)
    (Y : Type@{y}) (R : @HasRightValue@{u y e} A Y E)
  : Prop
  := @HasTwoValues@{u x y e} A X Y E L R.

(** Name an inherited parameter universe and keep a single instance
    of the equivalence in both branches. *)

Minks.Mixin HasNamedValues@{u e x y}
    (A : Type@{u}) (X : Type@{x}) (Y : Type@{y})
  extends HasLeftValue@{u x e} A X, HasRightValue@{u y e} A Y
  :=
  { named_left : X
  ; named_right : Y
  }.

(** Both parents select one equivalence when the universe graph equates its
    two named witness levels. Applying the class supplies that witness once. *)

Module EqualWitnessLevels.
Monomorphic Universe u e p x y.
Monomorphic Constraint e = p.

Minks.Mixin Shared (A : Type@{u}) (X : Type@{x}) (Y : Type@{y})
  extends HasLeftValue@{u x e} A X, HasRightValue@{u y p} A Y
  := { shared_value : X }.

Definition with_one_witness (A : Type@{u}) (X : Type@{x}) (Y : Type@{y})
    (E : HasEquiv@{u e} A)
    (L : @HasLeftValue@{u x e} A X E) (R : @HasRightValue@{u y p} A Y E)
  : Type
  := @Shared A X Y E L R.
End EqualWitnessLevels.

(** Strictly ordered witness levels cannot be shared. *)

Fail Minks.Mixin ConflictingLevels@{u e p x y | e < p}
    (A : Type@{u}) (X : Type@{x}) (Y : Type@{y})
  extends HasLeftValue@{u x e} A X, HasRightValue@{u y p} A Y
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

    Compare the family and carrier levels at strict sizes. Rocq infers
    the family level first in the complete record. *)

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
    (S : FixedPointFamily@{i u e})
  : FixedCarrier@{u e}
  := FixedPointFamilyToFixedCarrier S.

Definition fixed_parent_levels@{u e i | e < u, u < i}
    (S : FixedPointFamily@{i u e})
  : FixedPointed@{u e}
  := FixedPointFamilyToFixedPointed S.

(** The relative interface preserves the independent family level. *)

Definition fixed_export_levels@{u e i | i < u, u < e}
    (S : FixedPointFamily@{i u e})
  : HasFixedFamilyChoice@{u e i}
      (FixedPointFamilyToFixedCarrier S) (FixedPointFamily_hasFixedPoint S)
  := FixedPointFamilyToHasFixedFamilyChoice S.

(** A packed base preserves its carrier levels and the separate family level. *)

Definition packed_export_levels@{u e i | i < u, u < e}
    (S : FixedPointFamily@{i u e})
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
    (M : @HasFixedFamilyMember@{u e i} S P F)
  : @fixed_family S F (@fixed_point S P)
  := @fixed_family_member S P F M.

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

(** A native family and a chosen family of witnesses share two lower
    bounds. Projecting the native family from an unannotated bundle must
    still accept a strictly larger witness bound. *)

Module IndependentFieldBound.

Record Family@{h p l | h <= l, p <= l}
  := { index : Type@{h}
     ; relation : index -> index -> Type@{p}
     ; fiber : index -> Type@{l} }.

Minks.Mixin HasChoice@{h p l t | h <= l, p <= l, h <= t, p <= t, Set <= t}
    (A : Family@{h p l})
  := { choice : index A -> Type@{t} }.

Minks.Struct ChosenFamily
  extends Family
  with  chosen : HasChoice.

Definition underlying (F : ChosenFamily)
  := ChosenFamilyToFamily F.

Example larger_choice_bound@{h p l t | h < p, p < l, l < t}
    (A : Family@{h p l}) (W : HasChoice@{h p l t} A)
  : underlying (MakeChosenFamily A W) = A
  := eq_refl.

(** The same fields in a handwritten record have the same positional
    universe interface, including the independent witness bound. *)

Record NativeChosenFamily :=
  { native_base : Family
  ; native_choice : HasChoice native_base
  ; _ := MakeFamilyCarrier native_base }.

Definition compare_inferred_bounds@{t h p l | h < p, p < l, l < t}
    (F : ChosenFamily@{t h p l})
  : NativeChosenFamily@{t h p l}
  := Build_NativeChosenFamily (ChosenFamilyToFamily F) (ChosenFamily_chosen F).

Fail Record ConflictingNative@{h p l t | l < h} :=
  { rejected_base : Family@{h p l}
  ; rejected_choice : HasChoice@{h p l t} rejected_base }.

Fail Minks.Struct Conflicting@{h p l t | l < h}
  extends Family@{h p l}
  with  rejectedChoice : HasChoice@{h p l t}.

(** A closed constraint list is used as written. Omitting [Set <= t]
    lets Rocq minimize the two bounds in this unannotated client. *)

Minks.Struct ClosedFamily@{h p l t | h <= l, p <= l, h <= t, p <= t}
  extends Family@{h p l}
  with  closedChoice : HasChoice@{h p l t}.

Definition closed_underlying (F : ClosedFamily)
  := ClosedFamilyToFamily F.

Fail Definition closed_larger_bound@{h p l t | h < p, p < l, l < t}
    (A : Family@{h p l}) (W : HasChoice@{h p l t} A)
  := closed_underlying (MakeClosedFamily A W).

End IndependentFieldBound.

(** With universe polymorphism disabled, inferred levels are fixed. *)

Unset Universe Polymorphism.

Minks.Mixin HasFixedLevels (A : Type)
  :=
  { fixed_value : A }.

Check HasFixedLevels.
Fail Check HasFixedLevels@{Set}.

(** Struct headers can name levels even when the ambient option is off. *)

Minks.Struct NamedIndex@{u} (A : Type@{u}).
Check NamedIndex@{Set} nat.
Fail Minks.Struct TooFewLevels@{} (A : Type).
Minks.Struct OpenLevels@{u +} (A : Type@{u}) (B : Type).
Check OpenLevels@{Set Set} nat nat.

(** A constraint written only in the header restricts later applications,
    even when neither field nor parent imposes it. *)

Record NativeOrdered@{u v | u < v} (A : Type@{u}) (B : Type@{v}) := {}.
Minks.Struct Ordered@{u v | u < v} (A : Type@{u}) (B : Type@{v}).

Fail Check NativeOrdered@{Set Set}.
Fail Check Ordered@{Set Set}.

Minks.Struct NamedCarrier@{u}
  extends Type@{u}.

Minks.Struct NamedEquiv@{e u}
  extends NamedCarrier@{u}
  with  hasEquiv : HasEquiv@{u e}
  exports EquivOnCarrier [NamedCarrier].

Definition named_equiv_levels@{u e | u < e}
    (S : NamedEquiv@{e u})
  : HasEquiv@{u e} (NamedEquiv_carrier S)
  := NamedEquiv_hasEquiv S.

(** The parent view and the relative interface keep the declared level
    order. The public view can pack the same carrier at a higher level. *)

Definition named_parent_levels@{e u w | u < e, u < w}
    (S : NamedEquiv@{e u})
  : NamedCarrier@{w}
  := NamedEquivToNamedCarrier@{e u w} S.

Definition named_export_levels@{e u | u < e}
    (S : NamedEquiv@{e u})
  : EquivOnCarrier@{e u u} (NamedEquivToNamedCarrier@{e u u} S)
  := NamedEquivToEquivOnCarrier@{e u u} S.

Fail Minks.Struct ConflictingParentLevels@{u v | u < v}
  extends NamedCarrier@{u}, NamedCarrier@{v}.
