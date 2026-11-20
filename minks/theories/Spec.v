From elpi Require Import elpi.

(** * Structure specifications

    Store inheritance by Rocq identity. Each component key names one
    selected mixin and its dependencies within a structure. *)

(** * 结构规格

    用 Rocq 标识保存继承关系。在一个结构内，每个组件键指定一份 Mixin
    及其依赖。 *)

Elpi Db minks.flat.db lp:{{
  kind component type.
  type slot id -> gref -> list id -> component.

  kind mixin-param type.
  type mixin-carrier mixin-param.
  type mixin-value mixin-param.
  type mixin-dependency gref -> list int -> mixin-param.

  pred mixin-spec i:gref, o:list gref, o:list mixin-param.
  pred spec i:inductive, o:list inductive, o:list component.
  pred struct-view i:inductive, o:inductive, o:constant.
  pred flat-layout i:list string, i:option inductive, o:inductive, o:list component,
      o:list (pair id constant).
  pred fixed-carrier i:inductive, o:inductive.
}}.

Elpi File minks.spec lp:{{
  pred atom i:argument, o:id.
  atom (str Name) Name :-
    not (std.mem ["extends", "with", "as", ",", ":", "[", "]"] Name).

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
  mixin-head (mixin-dependency Ref _) Ref.

  pred mixin-arguments i:list mixin-param, i:list component, i:list id, o:list id.
  mixin-arguments [] _ Keys Keys.
  mixin-arguments [mixin-carrier | Params] Cs Keys Args :-
    mixin-arguments Params Cs {std.append Keys ["carrier"]} Args.
  mixin-arguments [mixin-dependency Ref Positions | Params] Cs Keys Args :-
    std.map Positions (i\k\ std.nth i Keys k) Deps,
    std.mem Cs (slot Key Ref Deps),
    mixin-arguments Params Cs {std.append Keys [Key]} Args.

  pred infer-mixin-arguments i:id, i:list mixin-param, i:list component, o:list id.
  infer-mixin-arguments Name Params Cs Args :-
    std.findall (mixin-arguments Params Cs [] _) Matches,
    if (Matches = [mixin-arguments _ _ _ Args]) true (
      if (Matches = [])
        (coq.error "Missing compatible dependencies for mixin:" Name)
        (coq.error "Ambiguous dependencies for mixin, give component keys:" Name)).

  pred print-mixin i:id, i:list gref, i:list mixin-param.
  print-mixin Name Direct Params :-
    Title is "Minks mixin " ^ Name,
    coq.say Title,
    std.map Direct coq.gref->id Parents,
    coq.say "Direct dependencies:" Parents,
    coq.say "Parameter order:" Params.

  pred carrier-of i:inductive, o:option inductive.
  carrier-of I (some Carrier) :- fixed-carrier I Carrier, !.
  carrier-of _ none.

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
}}.
