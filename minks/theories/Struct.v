From elpi Require Import elpi.
From Minks Require Import
  Spec
  Flat.

(** * Declare and inspect structures

    Declarations combine previously generated parents with new mixins.
    Inspection explains the component choices used by the generator. *)

(** * 声明并查看结构

    结构声明将已生成的父结构与新的 Mixin 组合。查看命令展示生成器使用的组件选择。 *)

Elpi Command minks.struct.
Elpi Accumulate Db Header minks.flat.db.
Elpi Accumulate File minks.spec.
Elpi Accumulate File minks.flat.
Elpi Accumulate lp:{{
  pred usage.
  usage :-
    coq.error "Usage: Minks.Struct Name [extends Parent, ...]"
      "[with key : Mixin [dependency, ...], ...].".

  pred parse-deps i:list argument, o:list id, o:list argument.
  parse-deps [str "[", str "]" | Rest] [] Rest :- !.
  parse-deps [str "[" | Rest] Deps Tail :- ids Rest Deps [str "]" | Tail].

  kind pending-slot type.
  type pending id -> id -> option (list id) -> option id -> pending-slot.

  pred slot-deps i:list argument, o:option (list id), o:list argument.
  slot-deps [str "[" | Rest] (some Keys) Tail :- !,
    parse-deps [str "[" | Rest] Keys Tail.
  slot-deps Args none Args.

  pred parse-slot i:list argument, o:pending-slot, o:list argument.
  parse-slot [A, str "as", F, str ":", B | Rest]
      (pending Key M Deps (some Field)) Tail :- !,
    atom A Key, atom F Field, atom B M, slot-deps Rest Deps Tail.
  parse-slot [A, str ":", B | Rest] (pending Key M Deps none) Tail :-
    atom A Key, atom B M, slot-deps Rest Deps Tail.

  pred parse-slots i:list argument, o:list pending-slot.
  parse-slots Args [Slot | Slots] :-
    parse-slot Args Slot Tail,
    (Tail = [], Slots = []
    ; Tail = [str "," | Rest], parse-slots Rest Slots).

  pred parse-components i:list argument, o:list pending-slot.
  parse-components [] [].
  parse-components [str "with" | Rest] Slots :- parse-slots Rest Slots.

  pred resolve-parent i:id, o:inductive.
  resolve-parent Name I :-
    coq.locate Name Ref,
    if (Ref = indt I) true (coq.error "Expected a parent type:" Name).

  pred inherited-components i:list inductive, o:list component.
  inherited-components [Parent] [] :- not (spec Parent _ _), !.
  inherited-components Parents Cs :- close-parents Parents Cs.

  pred resolve-slots i:list pending-slot, i:list component, o:list component.
  resolve-slots [] _ [].
  resolve-slots [pending Key M Selection _ | Slots] Available
      [slot Key Ref Deps | Rest] :-
    if (Key = "carrier") (coq.error "Reserved component key:" Key) true,
    coq.locate M Ref,
    if (mixin-spec Ref _ Params) true
      (coq.error "Component must be declared with Minks.Mixin:" M),
    if (Selection = some Keys)
      (Deps = Keys,
       if (mixin-arguments Params Available [] Keys) true
         (coq.error "Component keys do not match the mixin dependencies:" M))
      (infer-mixin-arguments M Params Available Deps),
    merge [slot Key Ref Deps] Available Next,
    resolve-slots Slots Next Rest.

  pred projection-names i:list pending-slot, o:list (pair id id).
  projection-names [] [].
  projection-names [pending Key _ _ (some Field) | Slots] [pr Key Field | Names] :-
    projection-names Slots Names.
  projection-names [pending _ _ _ none | Slots] Names :-
    projection-names Slots Names.

  pred save-views i:inductive, i:list (pair inductive constant).
  save-views I Views :-
    std.forall Views
      (v\ sigma a p\ v = pr a p,
        coq.elpi.accumulate execution-site "minks.flat.db"
          (clause _ _ (struct-view I a p))).

  pred build-structure i:id, i:list inductive, i:list component,
      i:list (pair id id), o:inductive, o:list inductive, o:option inductive,
      o:list (pair inductive constant).
  build-structure Name [Parent] [Component] Names I [] (some Parent) Views :-
    (@keep-alg-univs! => fixed-parent-mixin Parent Component ParentTy Mixin), !,
    component-key Component Key,
    if (std.mem Names (pr Key Field)) true (Field = Key),
    @keep-alg-univs! => pack-parent Name Parent Field ParentTy Mixin I Views.
  build-structure Name Parents Local Names I Parents Carrier Views :-
    shared-carrier Parents Carrier,
    close-parents Parents Inherited,
    merge Local Inherited Cs,
    generate Name Parents Cs Names Carrier I Views.

  main [A | Args] :-
    if (atom A Name, parse-parents Args ParentNames Rest,
        parse-components Rest Slots) true usage,
    std.map ParentNames resolve-parent Parents,
    inherited-components Parents Available,
    resolve-slots Slots Available Local,
    projection-names Slots Names,
    std.assert!
      (build-structure Name Parents Local Names I FlatParents Carrier Views)
      "Could not generate the structure",
    std.assert! (save-views I Views) "Could not register the ancestor views",
    if (Carrier = some Base)
      (coq.elpi.accumulate execution-site "minks.flat.db"
        (clause _ _ (fixed-carrier I Base))) true,
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (spec I FlatParents Local)).
  main _ :- usage.
}}.
Elpi Accumulate Db minks.flat.db.

Elpi Command minks.inspect.
Elpi Accumulate Db Header minks.flat.db.
Elpi Accumulate File minks.spec.
Elpi Accumulate lp:{{
  pred parent-sources i:list inductive, i:id, o:list id.
  parent-sources [] _ [].
  parent-sources [P | Ps] Key Sources :-
    close P Cs,
    parent-sources Ps Key Rest,
    if (std.mem Cs (slot Key _ _))
      (coq.gref->id (indt P) Name, Sources = [Name | Rest])
      (Sources = Rest).

  pred print-slot i:list inductive, i:list component, i:component.
  print-slot Parents Cs (slot Key Ref Deps) :-
    coq.gref->id Ref Mixin,
    parent-sources Parents Key Sources,
    DepText is "[" ^ {std.string.concat ", " Deps} ^ "]",
    if (Sources = []) (Suffix = " (declared here)")
      (Suffix is " (from " ^ {std.string.concat ", " Sources} ^ ")"),
    if (auto-instance Cs (slot Key Ref Deps))
      (Mode = " [instance]") (Mode = " [explicit]"),
    Line is "  " ^ Key ^ " : " ^ Mixin ^ " " ^ DepText ^ Suffix ^ Mode,
    coq.say Line.

  main [str Name] :- !,
    coq.locate Name Ref,
    if (mixin-spec Ref Direct Params)
      (print-mixin Name Direct Params) (
    if (Ref = indt I, spec I Parents _) true
      (coq.error "Not a Minks structure:" Name),
    close I Cs,
    if (Parents = [], fixed-carrier I Parent)
      (coq.gref->id (indt Parent) ParentName, Names = [ParentName])
      (std.map Parents (p\n\ coq.gref->id (indt p) n) Names),
    Title is "Minks structure " ^ Name,
    coq.say Title,
    if (Names = []) (coq.say "Direct parents: none")
      (Line is "Direct parents: " ^ {std.string.concat ", " Names},
       coq.say Line),
    coq.say "Packed fields:",
    if (fixed-carrier I Base)
      (coq.gref->id (indt Base) BaseName, CarrierLine is "  carrier : " ^ BaseName)
      (CarrierLine = "  carrier : Type"),
    coq.say CarrierLine,
    std.forall Cs (print-slot Parents Cs)).
  main _ :- coq.error "Usage: Minks.Inspect Name.".
}}.
Elpi Accumulate Db minks.flat.db.
