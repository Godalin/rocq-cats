From elpi Require Import elpi.
From Minks Require Import Spec.

(** * Flat structure generator

    The generator builds a flat record and direct forgetful maps from
    named components and their dependency graph. *)

Elpi File minks.flat lp:{{
  pred lookup i:id, i:list (pair id term), o:term.
  lookup Key Env T :-
    std.assert! (std.mem Env (pr Key T))
      ("Missing or out-of-order component " ^ Key).

  pred field-name i:id, i:id, o:id.
  field-name N Key F :- F is N ^ "_" ^ Key.

  pred component-type i:gref, i:list id, i:list (pair id term), o:term.
  component-type Ref Deps Env Ty :-
    coq.env.global Ref Head,
    std.map Deps (d\t\ lookup d Env t) Args,
    coq.mk-app Head Args Ty.

  pred fields i:id, i:list component, i:list (pair id id),
      i:list (pair id term), o:record-decl.
  fields _ [] _ _ end-record.
  fields N [slot Key Ref Ds | Cs] Names Env (field [] F Ty Tail) :-
    if (std.mem Names (pr Key F)) true (field-name N Key F),
    component-type Ref Ds Env Ty,
    pi x\ fields N Cs Names [pr Key x | Env] (Tail x).

  pred field-ref i:id, i:option constant, o:(pair id constant).
  field-ref Key (some C) (pr Key C).

  pred read-field i:list (pair id constant), i:id, o:term.
  read-field Fs Key Head :-
    std.mem Fs (pr Key C),
    coq.env.global (const C) Head.

  pred record-fields i:inductive, i:list id, o:list term.
  record-fields I Keys Fields :-
    coq.env.projections I Projections,
    std.map2 Keys Projections field-ref Refs,
    std.map Keys (k\t\ read-field Refs k t) Fields.

  pred apply-fields i:list term, i:term, o:list term.
  apply-fields [] _ [].
  apply-fields [F | Fs] X [app [F, X] | Ts] :-
    apply-fields Fs X Ts.

  pred view-body i:term, i:list term, o:(term -> term).
  view-body Ctor Fs (x\ app [Ctor | Args x]) :-
    pi x\ apply-fields Fs x (Args x).

  pred view-name i:id, i:inductive, o:id.
  view-name Child Ancestor Name :-
    coq.gref->id (indt Ancestor) AncestorName,
    Name is Child ^ "To" ^ AncestorName.

  pred declare-view i:id, i:term, i:inductive, i:(term -> term), o:constant.
  declare-view Child ChildTy Ancestor Body View :-
    Term = fun `child` ChildTy Body,
    view-name Child Ancestor Name,
    std.assert-ok! (coq.typecheck Term Ty) ("Ill-typed view " ^ Name),
    @univpoly! => coq.env.add-const Name Term Ty @transparent! View.

  pred flat-view-body i:list (pair id constant), i:inductive, i:list component,
      o:(term -> term).
  flat-view-body Fields Target Cs Body :-
    coq.env.indt Target tt 0 0 _ [K] _,
    coq.env.global (indc K) Ctor,
    std.map Cs component-key Keys,
    std.map ["carrier" | Keys] (k\t\ read-field Fields k t) Fs,
    view-body Ctor Fs Body.

  pred pack-components i:list component, i:list (pair id term),
      i:(list (pair id term) -> term -> prop), o:term.
  pack-components [] Env Build Term :- Build Env Term.
  pack-components [slot Key Ref Deps | Cs] Env Build (fun Name Ty Tail) :-
    component-type Ref Deps Env Ty,
    coq.id->name Key Name,
    pi x\ pack-components Cs [pr Key x | Env] Build (Tail x).

  pred pack-from-parent i:id, i:inductive, i:list component, i:inductive,
      o:constant.
  pack-from-parent Child I Cs Parent Pack :-
    coq.gref->id (indt Parent) ParentName,
    Name is Child ^ "Of" ^ ParentName,
    coq.env.global (indt Parent) ParentTy,
    coq.env.indt I tt 0 0 _ [K] _,
    coq.env.global (indc K) Ctor,
    close Parent ParentCs,
    std.map Cs component-key Keys,
    std.map ParentCs component-key ParentComponentKeys,
    ParentKeys = ["carrier" | ParentComponentKeys],
    record-fields Parent ParentKeys ParentFields,
    std.filter Cs (c\ not (std.mem ParentCs c)) Missing,
    Term = fun `parent` ParentTy Body,
    (pi p\ sigma inherited env\
      apply-fields ParentFields p inherited,
      std.map2 ParentKeys inherited (k\t\b\ b = pr k t) env,
      pack-components Missing env
        (bindings\result\ sigma args\
          std.map ["carrier" | Keys] (k\t\ lookup k bindings t) args,
          coq.mk-app Ctor args result)
        (Body p)),
    std.assert-ok! (coq.typecheck Term Ty) ("Ill-typed packing function " ^ Name),
    @univpoly! => coq.env.add-const Name Term Ty @transparent! Pack.

  % Canonical inference must preserve the child's explicit mixin choices.
  pred canonical-parent i:list component, i:list component.
  canonical-parent Child Parent :-
    std.forall Parent (c\ if (auto-instance Parent c) (auto-instance Child c) true).

  pred parent-view i:inductive, i:term, i:list (pair id constant),
      i:list component, i:list inductive, i:inductive, o:struct-conversion.
  parent-view I ChildTy Fields Cs Parents Parent (conversion I Parent View Mode) :-
    coq.gref->id (indt I) Child,
    close Parent ParentCs,
    flat-view-body Fields Parent ParentCs Body,
    declare-view Child ChildTy Parent Body View,
    if (canonical-parent Cs ParentCs)
      (if (std.mem Parents Parent) (Mode = coercion-canonical-view)
        (Mode = canonical-view))
      (if (std.mem Parents Parent) (Mode = coercion-view)
        (Mode = explicit-view)).

  pred register-parent-view i:struct-conversion.
  register-parent-view (conversion _ _ View Mode) :-
    if (std.mem [coercion-view, coercion-canonical-view] Mode)
      (@global! => coq.coercion.declare (coercion (const View) _ _ _))
      true,
    if (std.mem [canonical-view, coercion-canonical-view] Mode)
      (coq.CS.declare-instance (const View))
      true.

  pred strict-substructure i:list component, i:list component.
  strict-substructure Small Large :-
    std.length Small N,
    std.length Large M,
    N < M,
    std.forall Small (c\ std.mem Large c).

  pred inferred-view i:inductive, i:list (pair id constant), i:inductive,
      i:list component, o:constant.
  inferred-view Source Fields Target TargetCs View :-
    not (struct-view Source Target _ _),
    coq.gref->id (indt Source) From,
    view-name From Target Name,
    coq.env.current-path Here,
    std.append Here [Name] Path,
    std.string.concat "." Path Qualified,
    coq.locate-all Qualified [],
    coq.env.global (indt Source) SourceTy,
    flat-view-body Fields Target TargetCs Body,
    Term = fun `child` SourceTy Body,
    coq.typecheck Term Ty ok,
    @univpoly! => coq.env.add-const Name Term Ty @transparent! View.

  pred discover-views i:inductive, i:option inductive, i:list component,
      i:list (pair id constant), i:list struct-conversion,
      o:list struct-conversion.
  discover-views I Root Cs Fields Declared Views :-
    coq.env.current-path Here,
    std.findall (flat-layout Here Root _ _ _) Previous,
    std.map-filter Previous
      (layout\v\ sigma old old-cs old-fields view\
        layout = flat-layout Here Root old old-cs old-fields,
        strict-substructure Cs old-cs,
        inferred-view old old-fields I Cs view,
        v = conversion old I view explicit-view)
      Incoming,
    std.map-filter Previous
      (layout\v\ sigma old old-cs view\
        layout = flat-layout Here Root old old-cs _,
        strict-substructure old-cs Cs,
        not (std.mem Declared (conversion I old _ _)),
        inferred-view I Fields old old-cs view,
        v = conversion I old view explicit-view)
      Outgoing,
    std.append Outgoing Incoming Views,
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (flat-layout Here Root I Cs Fields)).

  pred register-field i:list component, i:list (pair id constant), i:bool, i:component.
  register-field Cs Fs Coerce (slot Key Ref Ds) :-
    if (auto-instance Cs (slot Key Ref Ds))
      (std.mem Fs (pr Key C),
       coq.TC.declare-instance (const C) 1,
       if (Coerce = tt)
         (@global! => @reversible! => coq.coercion.declare (coercion (const C) _ _ _))
         true)
      true.

  pred packed-sort i:sort, i:sort, o:sort.
  packed-sort (typ U) (typ V) (typ R) :- !, coq.univ.alg-max U V R.
  packed-sort _ (typ V) (typ V) :- !.
  packed-sort (typ U) _ (typ U) :- !.
  packed-sort _ _ prop.

  pred field-sorts i:record-decl, i:sort, o:sort.
  field-sorts end-record Sort Sort.
  field-sorts (field _ F Ty Tail) Current Sort :-
    std.assert-ok! (coq.typecheck-ty Ty FieldSort) ("Ill-typed field " ^ F),
    packed-sort Current FieldSort Next,
    coq.id->name F Name,
    pi x\ @pi-decl Name Ty x\ field-sorts (Tail x) Next Sort.

  pred packed-carrier i:option inductive, o:term.
  packed-carrier none (sort (typ U)) :- coq.univ.new U.
  packed-carrier (some Root) Carrier :- coq.env.global (indt Root) Carrier.

  % Read the carrier instance after field typing has unified its levels.
  pred carrier-levels i:term, o:list univ.variable.
  carrier-levels Carrier Levels :-
    Carrier = pglobal _ _, !,
    coq.reduction.lazy.whd Carrier (pglobal _ Instance),
    coq.univ-instance Instance Inherited,
    std.filter Inherited
      (l\ sigma u\ coq.univ.variable u l, not (coq.univ.global? u)) Local,
    std.fold Local [] (l\seen\out\ if (std.mem seen l) (out = seen)
      (out = [l | seen])) Reversed,
    std.rev Reversed Levels.
  carrier-levels _ [].

  pred fixed-record-sort i:term, i:(term -> record-decl), o:sort.
  fixed-record-sort Carrier Fields Sort :-
    std.assert-ok! (coq.typecheck-ty Carrier BaseSort) "Ill-typed carrier",
    pi x\ @pi-decl `carrier` Carrier x\ field-sorts (Fields x) BaseSort Sort.

  pred generate i:id, i:list inductive, i:list component, i:list (pair id id),
      i:option inductive, o:inductive, o:list struct-conversion, o:list constant.
  generate N Parents Cs Names none I Views Packers :-
    generate-record N Parents Cs Names none I Views Packers.
  generate N Parents Cs Names (some Root) I Views Packers :-
    @keep-alg-univs! =>
      generate-record N Parents Cs Names (some Root) I Views Packers.

  pred generate-record i:id, i:list inductive, i:list component, i:list (pair id id),
      i:option inductive, o:inductive, o:list struct-conversion, o:list constant.
  generate-record N Parents Cs Names Root I Views Packers :-
    packed-carrier Root Carrier,
    if (Root = none) (coq.univ.new R, Sort = typ R) true,
    if (Root = some Base)
      (coq.gref->id (indt Base) BaseName, F is N ^ "To" ^ BaseName)
      (field-name N "carrier" F),
    (pi a\ fields N Cs Names [pr "carrier" a] (Tail a)),
    Ctor is "Make" ^ N,
    if (Root = some _) (fixed-record-sort Carrier Tail Sort) true,
    Decl = record N (sort Sort) Ctor (field [coercion regular] F Carrier Tail),
    std.assert-ok! (coq.typecheck-indt-decl Decl) ("Ill-typed structure " ^ N),
    carrier-levels Carrier Levels,
    (@udecl! Levels tt [] tt => coq.env.add-indt Decl I),
    coq.env.global (indt I) ChildTy,
    coq.env.projections I Projections,
    std.map Cs component-key Keys,
    std.map2 ["carrier" | Keys] Projections field-ref Fields,
    std.assert! (ancestors Parents [] Reversed) "Could not read the ancestors",
    std.rev Reversed Ancestors,
    std.map Ancestors
      (p\v\ std.assert! (parent-view I ChildTy Fields Cs Parents p v)
        "Could not generate an ancestor view") ParentViews,
    if (Root = some Base)
      (Projections = [some Projection | _],
        BaseViews = [conversion I Base Projection coercion-view])
      (BaseViews = []),
    std.append ParentViews BaseViews Declared,
    discover-views I Root Cs Fields Declared OtherViews,
    std.append Declared OtherViews Views,
    std.forall ParentViews register-parent-view,
    std.forall Cs (register-field Cs Fields ff),
    std.filter Ancestors (p\ std.mem Parents p) DirectParents,
    std.map DirectParents (p\f\ pack-from-parent N I Cs p f) Packers.
}}.
