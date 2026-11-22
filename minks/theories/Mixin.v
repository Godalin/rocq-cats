From elpi Require Import elpi.
From Minks Require Import Spec.

(** * Mixin declarations

    A mixin records ordinary parameters and selected dependencies.
    The parameter order comes from the Rocq type. *)

Elpi Command minks.mixin.
Elpi Accumulate Db Header minks.flat.db.
Elpi Accumulate Plugin "minks.combinations".
Elpi Accumulate File minks.spec.
Elpi Accumulate lp:{{
  pred dependency-closure i:list gref, i:list gref, o:list gref.
  dependency-closure [] Seen Seen.
  dependency-closure [Ref | Refs] Seen All :-
    if (std.mem Seen Ref) (dependency-closure Refs Seen All) (
      if (mixin-combination Ref _ Cs _)
        (std.fold Cs Seen
          (c\seen\out\ sigma head\
            if (c = slot _ (mixin-kind head) _, not (std.mem seen head))
              (out = [head | seen]) (out = seen)) Next,
         dependency-closure Refs Next All) (
      mixin-spec Ref Parents _,
      dependency-closure Parents [Ref | Seen] Next,
      dependency-closure Refs Next All)).

  pred register-mixin i:gref, i:list gref, i:list int.
  register-mixin Ref Direct Values :-
    coq.gref->id Ref Name,
    if (coq.TC.class? Ref) true (coq.error "Expected a class:" Name),
    std.assert! (read-mixin Ref Values Params)
      "Expected ordinary parameters and registered mixin dependencies",
    dependency-closure Direct [] Closure,
    std.forall Params
      (p\ sigma d\
        if (mixin-head p d)
          (if (std.mem Closure d) true
            (coq.error "Parameter is outside the declared dependencies:" d)) true),
    std.forall Closure
      (d\ if (std.exists Params (p\ mixin-head p d)) true
        (coq.error "Declared dependency is absent from the class parameters:" d)),
    print-mixin Name Direct Params.

  main [str Name] :-
    attributes Attrs,
    if (std.mem Attrs (attribute "minks.declaration" _)) true
      (coq.error "Use Minks.Mixin to declare and register a mixin."),
    coq.locate Name (indt I),
    minks.mixin-header I Direct Values,
    register-mixin (indt I) Direct Values.
}}.
Elpi Accumulate Db minks.flat.db.
