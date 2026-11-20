From elpi Require Import elpi.
From Minks Require Import Spec.

(** * Flat structure generator

    The generator builds a flat record and direct forgetful maps from
    named components and their dependency graph. *)

(** * 平铺结构生成器

    从具名组件及其依赖图生成平铺记录与直接忘却映射。 *)

Elpi File minks.flat lp:{{
  pred lookup i:id, i:list (pair id term), o:term.
  lookup Key Env T :-
    std.assert! (std.mem Env (pr Key T))
      ("Missing or out-of-order component " ^ Key).

  pred field-name i:id, i:id, o:id.
  field-name N Key F :- F is N ^ "_" ^ Key.

  pred fields i:id, i:list component, i:list (pair id id),
      i:list (pair id term), o:record-decl.
  fields _ [] _ _ end-record.
  fields N [slot Key Ref Ds | Cs] Names Env (field [] F Ty Tail) :-
    if (std.mem Names (pr Key F)) true (field-name N Key F),
    coq.env.global Ref Head,
    std.map Ds (d\t\ lookup d Env t) Args,
    coq.mk-app Head Args Ty,
    pi x\ fields N Cs Names [pr Key x | Env] (Tail x).

  pred field-ref i:id, i:option constant, o:(pair id constant).
  field-ref Key (some C) (pr Key C).

  pred read-field i:list (pair id constant), i:id, o:term.
  read-field Fs Key Head :-
    std.mem Fs (pr Key C),
    coq.env.global (const C) Head.

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

  pred parent-view i:id, i:term, i:list (pair id constant), i:inductive,
      o:(pair inductive constant).
  parent-view Child ChildTy Fields Parent (pr Parent View) :-
    close Parent Cs,
    flat-view-body Fields Parent Cs Body,
    declare-view Child ChildTy Parent Body View.

  pred strict-substructure i:list component, i:list component.
  strict-substructure Small Large :-
    std.length Small N,
    std.length Large M,
    N < M,
    std.forall Small (c\ std.mem Large c).

  pred inferred-view i:inductive, i:list (pair id constant), i:inductive,
      i:list component, o:constant.
  inferred-view Source Fields Target TargetCs View :-
    not (struct-view Source Target _),
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
      i:list (pair id constant), i:list (pair inductive constant),
      o:list (pair inductive constant).
  discover-views I Root Cs Fields Declared Views :-
    coq.env.current-path Here,
    std.findall (flat-layout Here Root _ _ _) Previous,
    std.forall Previous
      (layout\ sigma old old-cs old-fields view\
        layout = flat-layout Here Root old old-cs old-fields,
        if (strict-substructure Cs old-cs, inferred-view old old-fields I Cs view)
          (coq.elpi.accumulate execution-site "minks.flat.db"
            (clause _ _ (struct-view old I view))) true),
    std.map-filter Previous
      (layout\v\ sigma old old-cs view\
        layout = flat-layout Here Root old old-cs _,
        strict-substructure old-cs Cs,
        not (std.mem Declared (pr old _)),
        inferred-view I Fields old old-cs view,
        v = pr old view)
      Views,
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (flat-layout Here Root I Cs Fields)).

  pred carrier-views i:id, i:term, i:inductive, i:constant,
      o:list (pair inductive constant).
  carrier-views Child ChildTy Parent Projection [pr Parent Projection | Views] :-
    coq.env.global (const Projection) ToParent,
    std.findall (struct-view Parent _ _) Inherited,
    std.map Inherited
      (v\out\ sigma a p f b view\
        v = struct-view Parent a p,
        coq.env.global (const p) f,
        b = (x\ app [f, app [ToParent, x]]),
        declare-view Child ChildTy a b view,
        out = pr a view)
      Views.

  pred register-field i:list component, i:list (pair id constant), i:component.
  register-field Cs Fs (slot Key Ref Ds) :-
    if (auto-instance Cs (slot Key Ref Ds))
      (std.mem Fs (pr Key C), coq.TC.declare-instance (const C) 1)
      true.

  pred packed-sort i:sort, i:sort, o:sort.
  packed-sort (typ U) (typ V) (typ R) :- !, coq.univ.alg-max U V R.
  packed-sort _ (typ V) (typ V) :- !.
  packed-sort (typ U) _ (typ U) :- !.
  packed-sort _ _ prop.

  % Append extension levels after the parent levels in their existing order.
  pred parent-levels i:term, o:list univ.variable.
  parent-levels (pglobal _ Instance) Levels :- coq.univ-instance Instance Levels.
  parent-levels (global _) [].

  % A unary mixin on the complete parent can use that parent as the carrier.
  pred fixed-parent-mixin i:inductive, i:component, o:term, o:term.
  fixed-parent-mixin Parent (slot _ Ref ["carrier"]) ParentTy Mixin :-
    coq.env.global Ref Mixin,
    coq.typecheck Mixin MixinTy ok,
    MixinTy = prod _ ParentTy (_\ sort _),
    coq.env.global (indt Parent) ParentTy.

  pred pack-parent i:id, i:inductive, i:id, i:term, i:term, o:inductive,
      o:list (pair inductive constant).
  pack-parent N Parent Field ParentTy Mixin I Views :-
    coq.gref->id (indt Parent) ParentName,
    ParentField is N ^ "To" ^ ParentName,
    Ctor is N ^ "Of" ^ ParentName,
    std.assert-ok! (coq.typecheck-ty ParentTy ParentSort)
      ("Ill-typed parent " ^ ParentName),
    (pi x\ @pi-decl `parent` ParentTy x\
      std.assert-ok! (coq.typecheck-ty (app [Mixin, x]) MixinSort)
        ("Ill-typed extension " ^ Field)),
    packed-sort ParentSort MixinSort Sort,
    Decl = record N (sort Sort) Ctor
      (field [coercion regular] ParentField ParentTy
        (x\ field [] Field (app [Mixin, x]) (_\ end-record))),
    std.assert-ok! (coq.typecheck-indt-decl Decl) ("Ill-typed structure " ^ N),
    parent-levels ParentTy Levels,
    (@udecl! Levels tt [] tt => coq.env.add-indt Decl I),
    coq.env.projections I [some ParentProjection, some Projection],
    coq.TC.declare-instance (const Projection) 1,
    coq.env.global (indt I) ChildTy,
    carrier-views N ChildTy Parent ParentProjection Views.

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

  pred fixed-record-sort i:term, i:(term -> record-decl), o:sort.
  fixed-record-sort Carrier Fields Sort :-
    std.assert-ok! (coq.typecheck-ty Carrier BaseSort) "Ill-typed carrier",
    pi x\ @pi-decl `carrier` Carrier x\ field-sorts (Fields x) BaseSort Sort.

  pred generate i:id, i:list inductive, i:list component, i:list (pair id id),
      i:option inductive, o:inductive, o:list (pair inductive constant).
  generate N Parents Cs Names none I Views :-
    generate-record N Parents Cs Names none I Views.
  generate N Parents Cs Names (some Root) I Views :-
    @keep-alg-univs! => generate-record N Parents Cs Names (some Root) I Views.

  pred generate-record i:id, i:list inductive, i:list component, i:list (pair id id),
      i:option inductive, o:inductive, o:list (pair inductive constant).
  generate-record N Parents Cs Names Root I Views :-
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
    (@univpoly! => coq.env.add-indt Decl I),
    coq.env.global (indt I) ChildTy,
    coq.env.projections I Projections,
    std.map Cs component-key Keys,
    std.map2 ["carrier" | Keys] Projections field-ref Fields,
    std.assert! (ancestors Parents [] Reversed) "Could not read the ancestors",
    std.rev Reversed Ancestors,
    std.map Ancestors
      (p\v\ std.assert! (parent-view N ChildTy Fields p v)
        "Could not generate an ancestor view") ParentViews,
    if (Root = some Base)
      (Projections = [some Projection | _],
        carrier-views N ChildTy Base Projection BaseViews)
      (BaseViews = []),
    std.append ParentViews BaseViews Declared,
    discover-views I Root Cs Fields Declared OtherViews,
    std.append Declared OtherViews Views,
    std.forall Cs (register-field Cs Fields).
}}.
