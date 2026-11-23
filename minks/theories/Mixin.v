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
  pred register-mixin i:gref, i:list gref, i:list int, i:list gref.
  register-mixin Ref Direct Values Expected :-
    coq.gref->id Ref Name,
    if (coq.TC.class? Ref) true (coq.error "Expected a class:" Name),
    std.assert! (read-mixin Ref Values Params)
      "Expected ordinary parameters and registered mixin dependencies",
    std.map-filter Params mixin-head Actual,
    if (Actual = Expected) true
      (coq.error "The generated class has different witness parameters:" Actual Expected),
    print-mixin Name Direct Params.

  main [str Name | Witnesses] :-
    attributes Attrs,
    if (std.mem Attrs (attribute "minks.declaration" _)) true
      (coq.error "Use Minks.Mixin to declare and register a mixin."),
    coq.locate Name (indt I),
    minks.mixin-header I Direct Values,
    std.map Witnesses (w\r\ sigma n\ w = str n, coq.locate n r) Expected,
    register-mixin (indt I) Direct Values Expected.
}}.
Elpi Accumulate Db minks.flat.db.
