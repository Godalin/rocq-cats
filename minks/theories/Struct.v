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

  pred atom i:argument, o:id.
  atom (str Name) Name :-
    not (std.mem ["extends", "with", ",", ":", "[", "]"] Name).

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

  pred parse-deps i:list argument, o:list id, o:list argument.
  parse-deps [str "[", str "]" | Rest] [] Rest :- !.
  parse-deps [str "[" | Rest] Deps Tail :- ids Rest Deps [str "]" | Tail].

  kind pending-slot type.
  type pending id -> id -> list id -> pending-slot.

  pred parse-slot i:list argument, o:pending-slot, o:list argument.
  parse-slot [A, str ":", B | Rest] (pending Key M Deps) Tail :-
    atom A Key, atom B M, parse-deps Rest Deps Tail.

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
    if (Ref = indt I, spec I _ _) true
      (coq.error "Not a Minks structure:" Name).

  pred resolve-slot i:pending-slot, o:component.
  resolve-slot (pending Key M Deps) (slot Key Ref Deps) :-
    if (Key = "carrier") (coq.error "Reserved component key:" Key) true,
    coq.locate M Ref,
    if (coq.TC.class? Ref) true (coq.error "Mixin must be a Class:" M).

  main [A | Args] :-
    if (atom A Name, parse-parents Args ParentNames Rest,
        parse-components Rest Slots) true usage,
    std.map ParentNames resolve-parent Parents,
    std.map Slots resolve-slot Local,
    close-parents Parents [] Inherited,
    merge Local Inherited Cs,
    generate Name Parents Cs I,
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (spec I Parents Local)).
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
    if (Ref = indt I, spec I Parents _) true
      (coq.error "Not a Minks structure:" Name),
    close I Cs,
    std.map Parents (p\n\ coq.gref->id (indt p) n) Names,
    Title is "Minks structure " ^ Name,
    coq.say Title,
    if (Names = []) (coq.say "Direct parents: none")
      (Line is "Direct parents: " ^ {std.string.concat ", " Names},
       coq.say Line),
    coq.say "Packed fields:",
    coq.say "  carrier : Type",
    std.forall Cs (print-slot Parents Cs).
  main _ :- coq.error "Usage: Minks.Inspect Name.".
}}.
Elpi Accumulate Db minks.flat.db.
