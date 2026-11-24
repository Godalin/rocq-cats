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

(** Inheritance and inspection must reject incomplete field identities.
    The synthetic signature exists only within its query. *)

Module IncompleteMetadata.
Record Raw := PackRaw { raw : Type }.

Fail Elpi Query minks.struct lp:{{
  coq.locate "Raw" (indt I),
  struct-spec I [] [slot "raw" (native-kind sort-head) []] =>
    parent-names (named-parent I []) _.
}}.

Fail Elpi Query minks.inspect lp:{{
  coq.locate "Raw" (indt I),
  struct-spec I [] [slot "raw" (native-kind sort-head) []] =>
    field-names I [] => inspect "Raw" (indt I).
}}.
End IncompleteMetadata.

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

Fail Definition unindexed_extraction (s : InheritedLabelledSort)
  : AllParentFields
  := _.

Minks.Struct Reassembled
  with  : WholeLabelledSort.
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

Check MakeEndoMap : ∀ A, MapBetween A A → EndoMap A.
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

(** ** Declaring map families with ordinary header parameters

    Fix a source point. Both presentations store the same map and a chosen
    target point with its preservation law. The law is relative to the map. *)

Module MapHeaders.
Minks.Mixin MapsPoint (A B : Type) (a : A) (f : MapBetween A B)
  :=
  { image_point : B
  ; preserves_point : f a = image_point }.

Section PointedMaps.
Context {A : Type} (B : Type) (a : A).

Minks.Struct SectionMap
  extends PackedMap A B
  with  law : MapsPoint [A, B, a, carrier]
  exports SectionLaw [PackedMap].
End PointedMaps.

Minks.Struct HeaderMap {A : Type} (B : Type) (a : A)
  extends PackedMap A B
  with  law : MapsPoint [A, B, a, carrier]
  exports HeaderLaw [PackedMap].

(** The implicit source type is inferred in constructors, views, packers
    and exports. Each projection computes on the supplied witnesses. *)

Section CompareMaps.
Context {A : Type} (B : Type) (a : A)
  (f : MapBetween A B) (w : MapsPoint A B a f).

Example same_parent
  : HeaderMapToPackedMap (A := A) B a (MakeHeaderMap B a f w)
    = SectionMapToPackedMap B a (MakeSectionMap B a f w)
  := eq_refl.

Example same_exported_law (p : PackedMap A B)
    (v : MapsPoint A B a (PackedMapToMapBetween A B p))
  : HeaderLaw_law B a (HeaderMapToHeaderLaw B a (HeaderMapOfPackedMap B a p v))
    = SectionLaw_law B a (SectionMapToSectionLaw B a (SectionMapOfPackedMap B a p v))
  := eq_refl.

Example same_reassembled_map
  : HeaderMapToMapBetween B a
      (HeaderMapOfHeaderLaw B a (MakePackedMap A B f)
        (MakeHeaderLaw B a (MakePackedMap A B f) w))
    = SectionMapToMapBetween B a
      (SectionMapOfSectionLaw B a (MakePackedMap A B f)
        (MakeSectionLaw B a (MakePackedMap A B f) w))
  := eq_refl.
End CompareMaps.

(** A parent takes its implicit source by name. Failed declarations leave
    the ambient section usable; its endpoint is discharged before the
    child's own source and point. *)

Section AtTarget.
Variable T : Type.

Fail Minks.Struct Inherited (T : Type).
Fail Minks.Struct Inherited (X X : Type).
Fail Minks.Struct Inherited {X : Type} (x : X)
  extends HeaderMap T x.
Fail Minks.Struct Inherited {X : Type} (x : X)
  extends HeaderMap (A := X) (A := X) T x.

Minks.Struct Inherited {X : Type} (x : X)
  extends HeaderMap T x (A := X).
End AtTarget.

Check @InheritedToHeaderMap
  : ∀ T X (x : X), Inherited T x → HeaderMap T x.

(** A parent can take the underlying types of two bundled endpoints.
    Its ancestor views retain the projections from those same endpoints. *)

Record PointedType := { underlying :> Type; basepoint : underlying }.

Minks.Struct OnPointedTypes (P Q : PointedType) (x : P)
  extends HeaderMap (A := P) Q x.

Example underlying_map (P Q : PointedType) (x : P) (f : OnPointedTypes P Q x)
  : OnPointedTypesToMapBetween P Q x f
    = HeaderMapToMapBetween Q x (OnPointedTypesToHeaderMap P Q x f)
  := eq_refl.

(** Rocq also inserts ordinary coercion functions in parent arguments. *)

Record Label := { label_type : Type }.
Definition labelled_values (L : Label)
  := option (label_type L).
Coercion labelled_values : Label >-> Sortclass.

Minks.Struct LabelMap (P Q : Label)
  extends MapBetween P Q.
Minks.Struct LabelEndo (P : Label)
  extends LabelMap P P.
Check LabelEndoToMapBetween : ∀ P, LabelEndo P → MapBetween P P.

(** Expanding this relative export in a mixin or a structure preserves
    the coercion on the index of its choice field. *)

Minks.Mixin HasChoice (A : Type)
  := { choice : A }.

Minks.Struct Chosen (A : Type)
  with  familyChoice : HasChoice [A].
Minks.Struct LabelChoice (L : Label)
  extends Chosen L
  exports ChoiceAt [].

Minks.Mixin MarkChoice (L : Label)
  extends ChoiceAt L
  := { marked : bool }.

Minks.Struct MarkedChoice (L : Label)
  extends LabelChoice L
  with  mark : MarkChoice [L, familyChoice].
Check @MakeMarkedChoice
  : ∀ (L : Label) (p : HasChoice L), @MarkChoice L p → MarkedChoice L.

Fail Minks.Struct ReuseAtLabel (L : Label)
  with  : ChoiceAt [L].

Minks.Struct SameChoice (L : Label)
  with  [labelChoice] : ChoiceAt [L].
Check MakeSameChoice : ∀ L : Label, HasChoice L → SameChoice L.

(** A declared index survives even when no field uses it. *)

Minks.Struct Phantom (Unused : Type)
  extends Sorted
  exports PhantomFields [].
Check MakePhantom : ∀ A : Type, Type → Phantom A.
Check PhantomOfPhantomFields : ∀ A : Type, PhantomFields → Phantom A.

Minks.Struct Indexed {A : Type}
  extends Phantom A.
Fail Minks.Struct IncompatibleIndices (A B : Type)
  extends Indexed (A := A), Phantom B.
End MapHeaders.

(** Discovery aligns independently declared fields with the same contextual
    key. A different parameter telescope or a different selection needs a
    fresh key. *)

Module IndexedViews.
Minks.Mixin HasMap (A B : Type)
  := { chosen_map : A → B }.

Minks.Struct Maps (X Y : Type)
  with  map : HasMap [X, Y].

Fail Minks.Struct SwappedMaps (B A : Type)
  with  map : HasMap [A, B].
Fail Minks.Struct DiagonalMaps (X : Type)
  with  map : HasMap [X, X].
Fail Minks.Struct PhantomMaps (X Y Unused : Type)
  with  map : HasMap [X, Y].

Minks.Struct TaggedMaps (A B : Type)
  with  map : HasMap [A, B],
        mapTag : HasTag.

Check TaggedMapsToMaps : ∀ A B, TaggedMaps A B → Maps A B.

Minks.Struct LaterMaps (P Q : Type)
  with  map : HasMap [P, Q].

Example discovered_map (A B : Type) (m : TaggedMaps A B)
  : LaterMaps_map A B (TaggedMapsToLaterMaps A B m) = TaggedMaps_map A B m
  := eq_refl.
(** Independent views follow a renamed identity. A freshly declared key
    with the same public spelling still denotes its own component. *)

Minks.Struct RenamedMaps (X Y : Type)
  extends TaggedMaps X Y
  with  map as otherMap.

Example renamed_view (X Y : Type) (m : RenamedMaps X Y)
  : LaterMaps_map X Y (RenamedMapsToLaterMaps X Y m) = RenamedMaps_otherMap X Y m
  := eq_refl.

Minks.Struct IndependentMaps (X Y : Type)
  with  otherMap : HasMap [X, Y].
Fail Check RenamedMapsToIndependentMaps.
End IndexedViews.

(** Both native parents expose the same type by conversion. The child stores
    one field, including when a packer starts from the other spelling. *)

Module NativeAliases.
Record Object := MkObject {}.
Definition ObjectAlias := Object.
Minks.Struct Objects extends Object.
Minks.Struct Aliases extends ObjectAlias.
Minks.Struct Together extends Objects, Aliases.
Check MakeTogether : Object → Together.
Example from_alias (x : Aliases)
  : TogetherToObjects (TogetherOfAliases x) = MakeObjects (AliasesToObjectAlias x)
  := eq_refl.
End NativeAliases.

Module MetadataOnly.
Minks.Struct Phantom (A : Type).

Section Family.
Context (Index : Type).
Minks.Struct ViaParent extends Phantom Index.
Minks.Struct ViaAncestor extends ViaParent.
End Family.

(** The empty record retains its index through an anonymous parent definition.
    The public view is a separate function. *)

Elpi Query minks.struct lp:{{
  coq.locate "ViaParent" (indt I), coq.locate "ViaParentToPhantom" (const P),
  coq.env.projections I [none], minks.stored-projections I [],
  not (coq.env.projection? P _).
}}.
Minks.Struct Twice (I : Type)
  extends Phantom I, Phantom I.
Check MakeTwice : ∀ I, Twice I.
Check MakeViaParent : ∀ A, ViaParent A.
Check ViaParent : Type → Type.
Check ViaAncestor : Type → Type.
Check ViaParentToPhantom : ∀ A, ViaParent A → Phantom A.
End MetadataOnly.
