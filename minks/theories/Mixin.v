From elpi Require Import elpi.
From Minks Require Import Spec.

(** * Mixin declarations

    A mixin records how a class is indexed by the carrier and previously
    selected components. The parameter order comes from the Rocq type. *)

(** * Mixin 声明

    Mixin 记录类如何由载体及已选组件索引。参数顺序来自 Rocq 类型。 *)

Elpi Command minks.mixin.
Elpi Accumulate Db Header minks.flat.db.
Elpi Accumulate File minks.spec.
Elpi Accumulate lp:{{
  pred registered-mixin i:argument, o:gref.
  registered-mixin (str Name) Ref :-
    coq.locate Name Ref,
    if (mixin-spec Ref _ _) true (coq.error "Parent mixin must be registered:" Name).

  pred parameter-index i:list term, i:term, o:int.
  parameter-index [X | _] X 0 :- !.
  parameter-index [_ | Vars] X N :-
    parameter-index Vars X M,
    N is M + 1.

  pred read-dependencies i:term, i:list term, i:int, i:list int, o:list mixin-param.
  read-dependencies (prod _ _ Body) Vars Pos [Pos | Values] [mixin-value | Params] :- !,
    Next is Pos + 1,
    pi x\ read-dependencies (Body x) {std.append Vars [x]} Next Values Params.
  read-dependencies (sort _) _ _ [] [].
  read-dependencies (prod _ Ty Body) Vars Pos Values
      [mixin-dependency Ref Positions | Params] :-
    coq.safe-dest-app Ty Head Args,
    coq.env.global Ref Head,
    mixin-spec Ref _ _,
    std.map Args (a\i\ parameter-index Vars a i) Positions,
    Next is Pos + 1,
    pi x\ read-dependencies (Body x) {std.append Vars [x]} Next Values Params.

  pred read-mixin i:gref, i:list int, o:list mixin-param.
  read-mixin Ref Values [mixin-carrier | Params] :-
    coq.env.typeof Ref (prod _ _ Body),
    pi a\ read-dependencies (Body a) [a] 1 Values Params.

  pred dependency-closure i:list gref, i:list gref, o:list gref.
  dependency-closure [] Seen Seen.
  dependency-closure [Ref | Refs] Seen All :-
    if (std.mem Seen Ref) (dependency-closure Refs Seen All) (
      mixin-spec Ref Parents _,
      dependency-closure Parents [Ref | Seen] Next,
      dependency-closure Refs Next All).

  pred register-mixin i:gref, i:list gref, i:list int.
  register-mixin Ref Direct Values :-
    coq.gref->id Ref Name,
    if (coq.TC.class? Ref) true (coq.error "Expected a class:" Name),
    std.assert! (read-mixin Ref Values Params)
      "Expected a carrier and registered mixin parameters",
    dependency-closure Direct [] Closure,
    std.forall Params
      (p\ sigma d\
        if (mixin-head p d)
          (if (std.mem Closure d) true
            (coq.error "Parameter is outside the declared dependencies:" d)) true),
    std.forall Closure
      (d\ if (std.mem Params (mixin-dependency d _)) true
        (coq.error "Declared dependency is absent from the class parameters:" d)),
    if (mixin-spec Ref Other Previous)
      (if (Other = Direct, Previous = Params) true
        (coq.error "Mixin already registered with different dependencies:" Name))
      (coq.elpi.accumulate execution-site "minks.flat.db"
        (clause _ _ (mixin-spec Ref Direct Params))).

  pred split-values i:list argument, o:list int, o:list argument.
  split-values [int Pos | Args] [Pos | Values] Parents :- !,
    split-values Args Values Parents.
  split-values Parents [] Parents.

  main [str Name | Args] :-
    attributes Attrs,
    if (std.mem Attrs (attribute "minks.declaration" _)) true
      (coq.error "Use Minks.Mixin to declare and register a mixin."),
    split-values Args Values Parents,
    std.map Parents registered-mixin Direct,
    coq.locate Name Ref,
    register-mixin Ref Direct Values.
}}.
Elpi Accumulate Db minks.flat.db.

Declare ML Module "rocq-minks.plugin".
