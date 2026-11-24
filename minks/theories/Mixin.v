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
  % The vernacular elaborator only needs the constructor and each remaining
  % field's key and binder role, in the order of the exported layout.
  typeabbrev export-field (pair id (pair bool gref)).
  external pred minks.parent-combinations i:list gref,
      o:list (pair (list role) (option (pair gref (list export-field)))).
  minks.parent-combinations Parents Shapes :-
    std.map Parents (p\out\ sigma i ctor parts fields origins roles shape\
      p = indt i, out = pr roles shape,
      if (mixin-combination p _ _ parts ctor origins)
        (std.map2 parts origins export-field-info fields,
         shape = some (pr (indc ctor) fields), coq.env.indt i tt N _ _ _ _,
         std.map {std.iota N} (_\r\ r = none) roles)
        (shape = none, mixin-roles i _ roles)) Shapes.

  pred export-field-info i:component, i:constant, o:export-field.
  export-field-info (slot K Kind _) P (pr K (pr Ordinary (const P))) :-
    if (Kind = native-kind _) (Ordinary = tt) (Ordinary = ff).

  pred register-mixin i:gref, i:list int, i:list gref.
  register-mixin Ref Values Expected :-
    coq.gref->id Ref Name,
    if (coq.TC.class? Ref) true (coq.error "Expected a class:" Name),
    std.assert! (read-mixin Ref Values Params)
      "Expected ordinary parameters and registered mixin dependencies",
    std.map-filter Params mixin-head Actual,
    if (Actual = Expected) true
      (coq.error "The generated class has different witness parameters:" Actual Expected).

  pred role-args i:list argument, o:list role, o:list argument.
  role-args [str ":" | Rest] [] Rest.
  role-args [str "ordinary" | Args] [none | Rs] Rest :- role-args Args Rs Rest.
  role-args [str "witness" | Args] [some none | Rs] Rest :- role-args Args Rs Rest.
  role-args [str "selected", str K, str Projection | Args] [some (some (pr K P)) | Rs] Rest :-
    coq.locate Projection P, role-args Args Rs Rest.

  pred parent-args i:list argument, o:list gref, o:list argument.
  parent-args [str ":" | Rest] [] Rest :- !.
  parent-args [str Name | Args] [P | Ps] Rest :- coq.locate Name P, parent-args Args Ps Rest.

  main [str Name | Args] :-
    attributes Attrs,
    if (std.mem Attrs (attribute "minks.declaration" _)) true
      (coq.error "Use Minks.Mixin to declare and register a mixin."),
    coq.locate Name (indt I),
    role-args Args Roles Tail, parent-args Tail Parents Witnesses,
    std.map Witnesses (w\r\ sigma n\ w = str n, coq.locate n r) Expected,
    Data = primitive Parents Roles,
    (declared (indt I) Data => (mixin-header I _ Values, register-mixin (indt I) Values Expected)),
    coq.elpi.accumulate execution-site "minks.flat.db" (clause _ _ (declared (indt I) Data)).
}}.
Elpi Accumulate Db minks.flat.db.
