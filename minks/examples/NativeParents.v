From Stdlib Require Import Utf8.
From Minks Require Import all.

(** * Layouts contributed by direct parents *)

Set Universe Polymorphism.

Minks.Struct Empty.
Check MakeEmpty : Empty.
Fail Check Empty_carrier.

Minks.Mixin HasTag
  := { tag : bool }.

Minks.Struct Tagged
  extends Empty
  with  carrier : HasTag
  exports TagInterface.

Check MakeTagged : HasTag → Tagged.
Check MakeTagInterface : HasTag → TagInterface.
Check TaggedOfEmpty : Empty → HasTag → Tagged.

Example tag_round_trip (t : HasTag)
  : Tagged_carrier (TaggedOfTagInterface (TaggedToTagInterface (MakeTagged t))) = t
  := eq_refl.

Minks.Struct Sorted
  extends Type.

Minks.Inspect TypeCarrier.
Minks.Inspect Sorted.
Check SortedOfTypeCarrier : TypeCarrier → Sorted.

Minks.Struct AnotherSort
  extends Type.

Example shared_base (A : Type)
  : SortedToTypeCarrier (MakeSorted A) = AnotherSortToTypeCarrier (MakeAnotherSort A)
  := eq_refl.

Example base_coercion (S : Sorted)
  : ((S : TypeCarrier) : Type) = Sorted_carrier S
  := eq_refl.

(** A failed declaration rolls back its newly generated base. *)

Record Fresh := MakeFresh {}.
Fail Minks.Struct BadChild
  extends Fresh
  with  tag : HasTag [missing].
Fail Check FreshCarrier.
Minks.Struct GoodChild
  extends Fresh.
Check GoodChildToFreshCarrier : GoodChild → FreshCarrier.

Module OccupiedName.
Record Native := MakeNative {}.
Definition NativeCarrier := bool.
Fail Minks.Struct BadName
  extends Native.
End OccupiedName.

Fail Minks.Struct TaggedSort
  extends Tagged, Sorted.

(** The sort field occupies its inherited position in the constructor. *)

Minks.Struct EmptySort
  extends Empty, Sorted.

Check MakeEmptySort : Type → EmptySort.

Minks.Struct Labelled
  with  label : HasTag.

Minks.Struct LabelledSort
  extends Labelled, Sorted
  exports WholeLabelledSort [].
Check MakeLabelledSort : HasTag → Type → LabelledSort.
Check MakeWholeLabelledSort : HasTag → Type → WholeLabelledSort.

Minks.Struct InheritedLabelledSort
  extends LabelledSort
  exports FixedParentFields, AllParentFields [].

Check MakeFixedParentFields : ∀ (t : HasTag) (A : Type), FixedParentFields t A.
Check MakeAllParentFields : HasTag → Type → AllParentFields.

Minks.Struct Reassembled
  with  whole : WholeLabelledSort.
Check MakeReassembled : HasTag → Type → Reassembled.

Minks.Mixin WithDefault
  extends WholeLabelledSort
  :=
  { default_value : carrier }.

Check @WithDefault : HasTag → Type → Type.

Example empty_sort_round_trip (A : Type)
  : (MakeEmptySort A : Type) = A
  := eq_refl.

(** Reuse a native family with the same section arguments after discharge. *)

Record MapBetween (A B : Type)
  := MakeMapBetween { apply_map : A → B }.
Arguments apply_map {A B}.
Coercion apply_map : MapBetween >-> Funclass.

Section NativeFamily.
Context (A B : Type).

Minks.Struct EndoMap
  extends MapBetween A A.

Minks.Struct PackedMap
  extends MapBetween A B
  exports AnyMap [].

Minks.Mixin TracksMap
  extends AnyMap
  :=
  { map_input : A
  ; map_output : B := carrier map_input
  }.

End NativeFamily.

Minks.Inspect MapBetweenCarrier.
Check MapBetweenCarrier : Type → Type → Type.
Check @PackedMapToMapBetweenCarrier
  : ∀ A B, PackedMap A B → MapBetweenCarrier A B.

Section InheritedFamily.
Context (X Y : Type).

Minks.Struct ChildMap
  extends PackedMap X Y, MapBetween X Y.

Fail Minks.Struct WrongMap
  extends PackedMap X Y, MapBetween Y X.

Example child_map_computes (f : MapBetween X Y) (x : X)
  : (MakeChildMap f) x = f x
  := eq_refl.

End InheritedFamily.

Minks.Inspect ChildMap.
