From elpi Require Import elpi.

(** * Structure specifications

    Store inheritance by Rocq identity. Each component key names one
    selected mixin and its dependencies within a structure. *)

Elpi Db minks.flat.db lp:{{
  kind component type.
  type slot id -> gref -> list id -> component.

  kind mixin-param type.
  type mixin-val mixin-param.
  type mixin-dep gref -> list int -> mixin-param.

  pred mixin-spec i:gref, o:list gref, o:list mixin-param.
  pred mixin-combination o:gref, o:list component, o:list component, o:constructor.
  pred spec i:inductive, o:list inductive, o:list component.
  kind view-registration type.
  type explicit-view, coercion-view, canonical-view,
    coercion-canonical-view view-registration.

  kind struct-conversion type.
  type conversion inductive -> inductive -> constant -> view-registration
    -> struct-conversion.

  pred struct-view i:inductive, o:inductive, o:constant, o:view-registration.
  pred struct-packer i:inductive, o:constant.
  pred struct-export i:inductive, o:inductive, o:list id.
  pred packed-export i:gref, o:inductive, o:list component, o:list component.
  pred struct-assembly i:inductive, o:constant, o:list id.
  pred flat-layout i:list string, i:option inductive, o:inductive, o:list component,
      o:list (pair id constant).
  pred fixed-carrier i:inductive, o:inductive.
}}.

Elpi File minks.spec lp:{{
  pred atom i:argument, o:id.
  atom (str Name) Name :-
    not (std.mem ["extends", "with", "as", "exports", ",", ":", "[", "]"] Name).

  pred ids i:list argument, o:list id, o:list argument.
  ids [A | Rest] [Name | Names] Tail :-
    atom A Name,
    ids-rest Rest Names Tail.

  pred ids-rest i:list argument, o:list id, o:list argument.
  ids-rest [str "," | Rest] Names Tail :- !, ids Rest Names Tail.
  ids-rest Rest [] Rest.

  pred parse-parents i:list argument, o:list id, o:list argument.
  parse-parents [str "extends" | Rest] Names Tail :- !, ids Rest Names Tail.
  parse-parents Rest [] Rest.

  pred mixin-head i:mixin-param, o:gref.
  mixin-head (mixin-dep Ref _) Ref.

  pred mixin-arguments i:list mixin-param, i:list component, i:list (pair id term),
      i:list id, o:list id.
  mixin-arguments [] _ _ Keys Keys.
  mixin-arguments [mixin-val | Params] Cs Fields Keys Args :-
    std.mem Fields (pr Key _),
    mixin-arguments Params Cs Fields {std.append Keys [Key]} Args.
  mixin-arguments [mixin-dep Ref Positions | Params] Cs Fields Keys Args :-
    std.map Positions (i\k\ std.nth i Keys k) Deps,
    std.mem Cs (slot Key Ref Deps),
    mixin-arguments Params Cs Fields {std.append Keys [Key]} Args.

  pred match-component i:id, i:gref, i:list id, i:list component,
      i:list id, o:id.
  match-component Key Ref Deps Available Used Actual :-
    if (std.mem Available (slot Key Ref Deps), not (std.mem Used Key))
      (Actual = Key)
      (std.mem Available (slot Actual Ref Deps), not (std.mem Used Actual)).

  pred translate-key i:list (pair id id), i:id, o:id.
  translate-key Mapping Key Actual :- std.mem Mapping (pr Key Actual).

  pred mapped-components i:list component, i:list component,
      i:list (pair id id), i:list id, o:list id.
  mapped-components [] _ _ _ [].
  mapped-components [slot Key Ref Deps | Cs] Available Mapping Used
      [Actual | Args] :-
    std.map Deps (translate-key Mapping) ActualDeps,
    match-component Key Ref ActualDeps Available Used Actual,
    mapped-components Cs Available [pr Key Actual | Mapping] [Actual | Used] Args.

  pred print-mixin i:id, i:list gref, i:list mixin-param.
  print-mixin Name Direct Params :-
    Title is "Minks mixin " ^ Name,
    coq.say Title,
    std.map Direct coq.gref->id Parents,
    coq.say "Direct dependencies:" Parents,
    coq.say "Parameter order:" Params.

  pred print-combination i:gref.
  print-combination Ref :-
    if (mixin-combination Ref Fixed Parts _)
      (std.map Fixed component-key FixedKeys,
       coq.say "Fixed keys:" ["carrier" | FixedKeys],
       coq.say "Expanded components:",
       std.forall Parts (print-slot [] {std.append Fixed Parts} " [instance, Coercion]"))
      true.

  pred print-packed-export i:gref, i:inductive, i:list component, i:list component.
  print-packed-export Ref Base Fixed Remaining :-
    coq.gref->id Ref Name,
    coq.gref->id (indt Base) BaseName,
    Title is "Minks relative interface " ^ Name,
    coq.say Title,
    coq.say "Packed base:" BaseName,
    close Base Covered,
    std.append Covered {std.append Fixed Remaining} Components,
    if (Fixed = []) true (
      coq.say "Additional fixed components:",
      std.forall Fixed (print-slot [] Components " [fixed]")),
    coq.say "Remaining components:",
    std.forall Remaining (print-slot [] Components " [instance, Coercion]").

  pred carrier-of i:inductive, o:option inductive.
  carrier-of I (some Carrier) :- fixed-carrier I Carrier, !.
  carrier-of I none :- spec I _ _, !.
  carrier-of I (some I).

  pred shared-carrier i:list inductive, o:option inductive.
  shared-carrier [] none.
  shared-carrier [Parent | Parents] Carrier :-
    carrier-of Parent Carrier,
    std.forall Parents
      (p\ if (carrier-of p Other, Other = Carrier) true
        (coq.error "Parents must share the same carrier type:" p)).

  pred ancestors i:list inductive, i:list inductive, o:list inductive.
  ancestors [] Seen Seen.
  ancestors [P | Parents] Seen All :-
    if (std.mem Seen P) (ancestors Parents Seen All) (
      spec P More _,
      ancestors More [P | Seen] Next,
      ancestors Parents Next All).

  pred merge i:list component, i:list component, o:list component.
  merge [] Cs Cs.
  merge [slot Key Ref Deps | Rest] Cs Out :-
    if (std.mem Cs (slot Key _ _))
       (if (std.mem Cs (slot Key Ref Deps)) true
         (coq.error "Incompatible definitions of component" Key),
        merge Rest Cs Out)
       (merge Rest {std.append Cs [slot Key Ref Deps]} Out).

  pred close i:inductive, o:list component.
  close I Cs :-
    if (spec I Parents Local) true (coq.error "Not a Minks structure:" I),
    close-parents Parents Inherited,
    merge Local Inherited Cs.

  pred shared-component i:component, i:list (list component).
  shared-component C [Branch | Branches] :-
    if (std.mem Branch C)
      (std.exists Branches (b\ std.mem b C))
      (shared-component C Branches).

  pred close-parents i:list inductive, o:list component.
  close-parents Parents Cs :-
    std.map Parents close Branches,
    std.fold Branches [] merge Ordered,
    std.partition Ordered (c\ shared-component c Branches) Shared Rest,
    std.append Shared Rest Cs.

  % Only one slot for a class head may supply an automatic instance.
  % Different dependencies do not prove that two instance types are disjoint.
  pred auto-instance i:list component, i:component.
  auto-instance Cs (slot Key Ref _) :-
    coq.TC.class? Ref,
    not (std.exists Cs (c\ c = slot Other Ref _, not (Other = Key))).

  pred component-key i:component, o:id.
  component-key (slot Key _ _) Key.

  pred parent-sources i:list inductive, i:id, o:list id.
  parent-sources [] _ [].
  parent-sources [P | Ps] Key Sources :-
    close P Cs,
    parent-sources Ps Key Rest,
    if (std.mem Cs (slot Key _ _))
      (coq.gref->id (indt P) Name, Sources = [Name | Rest])
      (Sources = Rest).

  pred print-slot i:list inductive, i:list component, i:string, i:component.
  print-slot Parents Cs Registration (slot Key Ref Deps) :-
    coq.gref->id Ref Mixin,
    parent-sources Parents Key Sources,
    DepText is "[" ^ {std.string.concat ", " Deps} ^ "]",
    if (Sources = []) (Suffix = " (declared here)")
      (Suffix is " (from " ^ {std.string.concat ", " Sources} ^ ")"),
    if (auto-instance Cs (slot Key Ref Deps))
      (Mode = Registration) (Mode = " [explicit]"),
    Line is "  " ^ Key ^ " : " ^ Mixin ^ " " ^ DepText ^ Suffix ^ Mode,
    coq.say Line.

  pred registration-label i:view-registration, o:string.
  registration-label explicit-view "explicit".
  registration-label coercion-view "Coercion".
  registration-label canonical-view "Canonical".
  registration-label coercion-canonical-view "Coercion, Canonical".

  pred print-view i:struct-conversion.
  print-view (conversion _ _ Ref Registration) :-
    coq.gref->id (const Ref) Name,
    registration-label Registration Label,
    Line is "  " ^ Name ^ " [" ^ Label ^ "]",
    coq.say Line.

  pred print-packer i:constant.
  print-packer Ref :-
    coq.gref->id (const Ref) Name,
    Line is "  " ^ Name,
    coq.say Line.

  pred print-export i:(pair inductive (list id)).
  print-export (pr Export Keys) :-
    coq.gref->id (indt Export) Name,
    Line is "  " ^ Name ^ " [" ^ {std.string.concat ", " Keys} ^ "]",
    coq.say Line.

  pred print-struct i:id, i:list inductive, i:option inductive, i:list component,
      i:list struct-conversion, i:list constant, i:list (pair inductive (list id)),
      i:list (pair constant (list id)).
  print-struct Name Parents Carrier Cs Views Packers Exports Assemblies :-
    if (Parents = [], Carrier = some Base)
      (coq.gref->id (indt Base) BaseName, Names = [BaseName])
      (std.map Parents (p\n\ coq.gref->id (indt p) n) Names),
    Title is "Minks structure " ^ Name,
    coq.say Title,
    if (Names = []) (coq.say "Direct parents: none")
      (Line is "Direct parents: " ^ {std.string.concat ", " Names},
       coq.say Line),
    coq.say "Packed fields:",
    if (Carrier = some Root)
      (coq.gref->id (indt Root) RootName, CarrierLine is "  carrier : " ^ RootName)
      (CarrierLine = "  carrier : Type [Coercion]"),
    coq.say CarrierLine,
    std.forall Cs (print-slot Parents Cs " [instance]"),
    if (Views = []) true (coq.say "Conversions:", std.forall Views print-view),
    if (Packers = []) true
      (coq.say "Packing functions:", std.forall Packers print-packer),
    if (Exports = []) true
      (coq.say "Relative interfaces:", std.forall Exports print-export),
    if (Assemblies = []) true (
      coq.say "Assembled views:",
      std.forall Assemblies (a\ sigma ref keys label line\
        a = pr ref keys, coq.gref->id (const ref) label,
        line is "  " ^ label ^ " [" ^ {std.string.concat ", " keys} ^ "]",
        coq.say line)).
}}.
