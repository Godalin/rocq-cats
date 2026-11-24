From elpi Require Import elpi.
From Minks Require Import Spec.

(** * Flat structure generator

    The generator builds a flat record and direct forgetful maps from
    named components and their dependency graph. *)

Elpi File minks.flat lp:{{
  pred lookup i:id, i:list (pair id term), o:term.
  lookup Key _ T :- ambient-value Key T, !.
  lookup Key Env T :-
    std.assert! (std.mem Env (pr Key T))
      ("Missing or out-of-order component " ^ Key).

  pred field-name i:id, i:id, o:id.
  field-name N Key F :- F is N ^ "_" ^ Key.

  input-term Env (key-input Key) T :- lookup Key Env T.
  input-term Env (projection-input C Args) T :-
    std.map Args (input-term Env) Terms, coq.env.global (const C) Head,
    coq.mk-app Head Terms T.

  input-term Env (host-input Expr Inputs) T :-
    std.map Inputs (input-term Env) Args, open-scoped Expr Args T.

  pred component-type i:gref, i:list input, i:list (pair id term), o:term.
  component-type Ref Deps Env Ty :-
    coq.env.global Ref Head,
    std.map Deps (input-term Env) Args,
    coq.mk-app Head Args Ty.

  pred selected-head i:id, i:field-kind, o:term.
  field-type (slot Key Kind Args) Env Ty :-
    selected-head Key Kind Head, !,
    std.map Args (input-term Env) Terms, coq.mk-app Head Terms Ty.
  field-type (slot _ (mixin-kind Ref) Args) Env Ty :- component-type Ref Args Env Ty.
  field-type (slot _ (native-kind (ref-head Ref)) Args) Env Ty :- component-type Ref Args Env Ty.
  field-type (slot _ (native-kind sort-head) []) _ (sort (typ U)) :- coq.univ.new U.

  pred projection-id i:id, i:component, o:id.
  projection-id N (slot _ (native-kind (ref-head Ref)) _) F :- !,
    coq.gref->id Ref Head, F is N ^ "To" ^ Head.
  projection-id N C F :- component-key C K, field-name N K F.

  pred fields i:id, i:list component, i:list (pair id id),
      i:list (pair id term), o:record-decl.
  fields _ [] _ _ end-record.
  fields N [C | Cs] Names Env (field [] F Ty Tail) :-
    component-key C Key,
    if (std.mem Names (pr Key F)) true (projection-id N C F),
    field-type C Env Ty,
    pi x\ fields N Cs Names [pr Key x | Env] (Tail x).

  pred field-ref i:id, i:option constant, o:(pair id constant).
  field-ref Key (some C) (pr Key C).

  % Declarations generated together share the universe prefix of their header.
  pred header-universes o:list univ.variable.
  header-universes [].

  pred header-global i:gref, o:term.
  header-global Ref Head :-
    header-universes Levels, coq.env.global Ref Fresh,
    if (Levels = []) (Head = Fresh) (
      Fresh = pglobal _ Original, coq.univ-instance Original Vars,
      std.length Levels N, std.drop N Vars Tail,
      coq.univ-instance Instance {std.append Levels Tail},
      @uinstance! Instance => coq.env.global Ref Head).

  pred active-family o:inductive, o:list term.
  pred family-global i:gref, o:term.
  family-global Ref T :-
    if (active-family I Args,
        (Ref = indt I ; coq.env.indt I tt _ _ _ [K] _, Ref = indc K ;
         Ref = const P, coq.env.projections I Ps, std.mem Ps (some P)))
      (header-global Ref Head, coq.mk-app Head Args T) (coq.env.global Ref T).

  pred read-field i:list (pair id constant), i:id, o:term.
  read-field Fs Key Head :-
    std.mem Fs (pr Key C),
    family-global (const C) Head.

  pred parent-global i:inductive, i:gref, o:term.
  parent-global I Ref Applied :-
    coq.env.indt I tt Arity _ _ _ _,
    if (parent-inputs I Args) true (Args = []),
    std.length Args Arity, coq.env.global Ref Head, coq.mk-app Head Args Applied.

  pred stored-fields i:inductive, i:list id, o:list (pair id constant).
  stored-fields I Keys Refs :-
    minks.stored-projections I Ps,
    std.map2 Keys Ps (k\p\r\ sigma c\ p = const c, r = pr k c) Refs.

  pred record-fields i:inductive, i:list id, o:list term.
  record-fields I Keys Fields :-
    stored-fields I Keys Refs,
    std.map Keys (k\t\ sigma c\ std.mem Refs (pr k c), parent-global I (const c) t) Fields.

  pred apply-fields i:list term, i:term, o:list term.
  apply-fields [] _ [].
  apply-fields [F | Fs] X [app [F, X] | Ts] :-
    apply-fields Fs X Ts.

  pred view-body i:term, i:list term, o:(term -> term).
  view-body Ctor Fs Body :-
    pi x\ sigma args\ apply-fields Fs x args, coq.mk-app Ctor args (Body x).

  pred view-name i:id, i:inductive, o:id.
  view-name Child Ancestor Name :-
    coq.gref->id (indt Ancestor) AncestorName,
    Name is Child ^ "To" ^ AncestorName.

  pred declare-view i:id, i:term, i:inductive, i:(term -> term), o:constant.
  declare-view Child ChildTy Ancestor Body View :-
    Term = fun `child` ChildTy Body,
    view-name Child Ancestor Name,
    declare-map Name Term View.

  pred flat-view-body i:list (pair id constant), i:inductive, i:list component,
      o:(term -> term).
  flat-view-body Fields Target Cs Body :-
    coq.env.indt Target tt _ _ _ [K] _,
    parent-global Target (indc K) Ctor,
    std.map Cs component-key Keys,
    std.map Keys (k\t\ read-field Fields k t) Fs,
    view-body Ctor Fs Body.

  pred pack-components i:list component, i:list (pair id term),
      i:(list (pair id term) -> term -> prop), o:term.
  pack-components [] Env Build Term :- Build Env Term.
  pack-components [C | Cs] Env Build (fun Name Ty Tail) :-
    component-key C Key, field-type C Env Ty,
    coq.id->name Key Name,
    pi x\ pack-components Cs [pr Key x | Env] Build (Tail x).

  pred pack-from-parent i:id, i:inductive, i:list component, i:inductive,
      o:constant.
  pack-from-parent Child I Cs Parent Pack :-
    coq.gref->id (indt Parent) ParentName,
    Name is Child ^ "Of" ^ ParentName,
    parent-global Parent (indt Parent) ParentTy,
    coq.env.indt I tt _ _ _ [K] _,
    family-global (indc K) Ctor,
    close Parent ParentCs,
    std.map Cs component-key Keys,
    std.map ParentCs component-key ParentKeys,
    record-fields Parent ParentKeys ParentFields,
    std.filter Cs (c\ not (contains-key {component-key c} ParentCs)) Missing,
    Term = fun `parent` ParentTy Body,
    (pi p\ sigma inherited env\
      apply-fields ParentFields p inherited,
      std.map2 ParentKeys inherited (k\t\b\ b = pr k t) env,
      pack-components Missing env
        (bindings\result\ sigma args\
          std.map Keys (k\t\ lookup k bindings t) args,
          coq.mk-app Ctor args result)
        (Body p)),
    declare-map Name Term Pack.

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
    if (ParentCs = [_ | _], canonical-parent Cs ParentCs)
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

  % Use rigid symbols for source parameter and field identities. Target
  % formals are pattern variables shared by all their occurrences. The
  % resulting substitution is checked on the actual Rocq constructor below.
  pred with-symbols i:list id, i:list (pair id term), i:(list (pair id term) -> prop).
  with-symbols [] Env K :- K Env.
  with-symbols [Key | Keys] Env K :-
    pi symbol\ with-symbols Keys [pr Key symbol | Env] K.

  pred pattern-term i:list (pair id term), i:input, o:term.
  pattern-term Env (key-input Key) T :-
    if (std.mem Env (pr Key T)) true (ambient-value Key T).
  pattern-term Env (projection-input P Inputs) T :-
    std.map Inputs (pattern-term Env) Args, coq.mk-app (global (const P)) Args T.
  pattern-term Env (host-input Expr Inputs) T :-
    std.map Inputs (pattern-term Env) Args, pattern-body Expr Shape,
    open-scoped Shape Args T.

  % Compare binding positions independently of the fresh universe instances.
  pred pattern-body i:scoped-term, o:scoped-term.
  pattern-body (scope-arg Body) (scope-arg Rest) :-
    pi x\ pattern-body (Body x) (Rest x).
  pattern-body (scope-body Body) (scope-body T) :-
    (pi ref u\ copy (pglobal ref u) (global ref) :- !) => copy Body T.

  pred match-descriptor i:list (pair id term), i:list (pair id term),
      i:list component, i:component, i:id.
  match-descriptor Source Target Cs (slot _ Kind Inputs) Key :-
    std.mem Cs (slot Key Other Actual),
    if (Kind = mixin-kind _) (Kind = Other) (Other = native-kind _),
    std.map Inputs (pattern-term Target) Patterns,
    std.map Actual (pattern-term Source) Terms, Patterns = Terms.

  pred view-indices i:inductive, i:list component, i:inductive, i:list component, i:list id,
      o:list int.
  view-indices Source Cs Target Hs Aligned Positions :-
    current-layout Source 0 Cs Names SourceCs,
    current-layout Target 0 Hs Formals TargetCs,
    std.map Names parameter-key SourceKeys, std.map Formals parameter-key TargetKeys,
    std.map Cs component-key Fields,
    with-symbols {std.append SourceKeys Fields} [] (env\ sigma bindings common target symbols\
      std.map SourceKeys (k\x\ std.mem env (pr k x)) symbols,
      std.map TargetKeys (k\p\ sigma x\ p = pr k x) bindings,
      std.map2 TargetCs Aligned (c\k\p\ sigma x\ std.mem env (pr k x),
        p = pr {component-key c} x) common,
      std.append bindings common target,
      std.forall2 TargetCs Aligned (match-descriptor env target SourceCs),
      std.map bindings (p\i\ sigma actual\ p = pr _ actual, not (var actual),
        parameter-index symbols actual i) Positions).

  pred inferred-body i:term, i:term, i:list term, i:list int,
      i:list (pair id constant), i:list id, i:constructor, o:term.
  inferred-body (prod Name Ty Body) Applied Params Positions Fields Keys K
      (fun Name Ty Rest) :- !,
    pi x\ inferred-body (Body x) Applied {std.append Params [x]} Positions
      Fields Keys K (Rest x).
  inferred-body _ Head Params Positions Fields Keys K (fun `child` Ty Body) :-
    coq.mk-app Head Params Ty,
    std.map Positions (i\t\ std.nth i Params t) Actuals,
    coq.env.global (indc K) Make, coq.mk-app Make Actuals Ctor,
    std.map Keys (key\p\ sigma c proj\ std.mem Fields (pr key c),
      coq.env.global (const c) proj, coq.mk-app proj Params p) Projections,
    view-body Ctor Projections Body.

  pred inferred-view i:inductive, i:list component, i:list (pair id constant),
      i:inductive, i:list component, o:constant.
  inferred-view Source Cs Fields Target TargetCs View :-
    std.length TargetCs N, std.length Cs M, N < M,
    not (struct-view Source Target _ _),
    coq.gref->id (indt Source) From, view-name From Target Name,
    coq.env.current-path Here, std.append Here [Name] Path,
    std.string.concat "." Path Qualified, coq.locate-all Qualified [],
    minks.stored-projections Target Projections,
    std.map Projections (p\k\ sigma c\ std.mem Fields (pr k c),
      minks.same-key (const c) p) Keys,
    view-indices Source Cs Target TargetCs Keys Positions,
    coq.env.indt Target tt _ _ _ [K] _,
    coq.env.global (indt Source) Head, coq.typecheck Head Arity ok,
    inferred-body Arity Head [] Positions Fields Keys K Term,
    coq.typecheck Term Ty ok,
    @univpoly! => coq.env.add-const Name Term Ty @transparent! View.

  pred discover-views i:inductive, i:list component,
      i:list (pair id constant), i:list struct-conversion,
      o:list struct-conversion.
  discover-views I Cs Fields Declared Views :-
    coq.env.current-path Here,
    std.findall (flat-layout Here _ _ _) Previous,
    std.map-filter Previous
      (layout\v\ sigma old old-cs old-fields view\
        layout = flat-layout Here old old-cs old-fields,
        inferred-view old old-cs old-fields I Cs view,
        v = conversion old I view explicit-view)
      Incoming,
    std.map-filter Previous
      (layout\v\ sigma old old-cs view\
        layout = flat-layout Here old old-cs _,
        not (std.mem Declared (conversion I old _ _)),
        inferred-view I Cs Fields old old-cs view,
        v = conversion I old view explicit-view)
      Outgoing,
    std.append Outgoing Incoming Views,
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (flat-layout Here I Cs Fields)).

  pred register-field i:int, i:list component, i:list (pair id constant), i:component.
  register-field Priority Cs Fs (slot Key (mixin-kind Ref) Ds) :-
    if (auto-instance Cs (slot Key (mixin-kind Ref) Ds))
      (std.mem Fs (pr Key C), coq.TC.declare-instance (const C) Priority)
      true.
  register-field _ _ Fs (slot Key (native-kind _) _) :-
    std.mem Fs (pr Key C),
    @global! => @reversible! => coq.coercion.declare (coercion (const C) _ _ _).

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

  % Normalize the instance after field typing has unified its levels.
  pred head-levels i:term, o:list univ.variable.
  head-levels Ty Levels :-
    coq.safe-dest-app Ty Head _, Head = pglobal _ _, !,
    coq.reduction.lazy.whd Head (pglobal _ Instance),
    coq.univ-instance Instance Inherited,
    std.filter Inherited
      (l\ sigma u\ coq.univ.variable u l, not (coq.univ.global? u)) Local,
    std.fold Local [] (l\seen\out\ if (std.mem seen l) (out = seen)
      (out = [l | seen])) Reversed,
    std.rev Reversed Levels.
  head-levels _ [].

  % Keep the levels of native field heads in their original order.
  pred layout-levels i:list component, i:record-decl, o:list univ.variable.
  layout-levels [] end-record [].
  layout-levels [C | Cs] (field _ _ Ty Body) Levels :-
    if (C = slot _ (native-kind sort-head) [], coq.reduction.lazy.whd Ty (sort (typ U)),
        not (coq.univ.global? U), coq.univ.variable U L) (Current = [L])
      (if (C = slot _ (native-kind _) _) (head-levels Ty Current) (Current = [])),
    pi x\ layout-levels Cs (Body x) Rest,
    std.filter Rest (l\ not (std.mem Current l)) New, std.append Current New Levels.

  % Abstract the native head's own telescope, independently of the first use.
  pred unused-binder i:id, i:list id, o:id.
  unused-binder Name Used Key :-
    if (std.mem Used Name)
      (Next is Name ^ "'", unused-binder Next Used Key) (Key = Name).

  pred base-record i:id, i:native-head, i:term, i:term, i:list id,
      o:indt-decl, o:list id.
  base-record N Head T (prod Binder Ty Rest) Rev (parameter Key explicit Ty Tail) Keys :- !,
    coq.name->id Binder Hint,
    if (Hint = "_") (Stem = "arg") (Stem = Hint), unused-binder Stem Rev Key,
    pi x\ @pi-parameter Key Ty x\ sigma app\
      coq.mk-app T [x] app,
      base-record N Head app (Rest x) [Key | Rev] (Tail x) Keys.
  base-record N Head T (sort _) Rev (record N (sort S) Ctor Body) Keys :- !,
    std.rev Rev Names, std.map Names parameter-key Keys,
    std.assert-ok! (coq.typecheck-ty T S) "Expected a native type",
    projection-id N (slot "carrier" (native-kind Head) {key-inputs Keys}) Projection,
    Ctor is "Make" ^ N, Body = field [] Projection T (_\ end-record).

  base-record N Head T Arity Rev Decl Keys :-
    coq.reduction.lazy.whd Arity Telescope,
    (Telescope = prod _ _ _ ; Telescope = sort _),
    base-record N Head T Telescope Rev Decl Keys.

  pred generate-base i:native-head, o:inductive, o:list component.
  generate-base Head I Cs :- @keep-alg-univs! ==>
    parent-label (native-parent Head []) Label, Name is Label ^ "Carrier",
    field-type (slot "carrier" (native-kind Head) []) [] T,
    std.assert-ok! (coq.typecheck T Arity) "Ill-typed native parent",
    base-record Name Head T Arity [] Decl Keys,
    std.assert-ok! (coq.typecheck-indt-decl Decl) ("Ill-typed native base " ^ Name),
    head-levels T Levels, (@udecl! Levels tt [] tt => coq.env.add-indt Decl I),
    if (Head = ref-head Ref, coq.arguments.implicit Ref Imps, Imps = [_ | _])
      (@global! => coq.arguments.set-implicit (indt I) Imps) true,
    C = slot "carrier" (native-kind Head) {key-inputs Keys}, Cs = [C],
    coq.env.projections I [some P], register-field 1 Cs [pr "carrier" P] C.

  pred struct-universes o:upoly-decl.
  pred bind-header i:list header-binder, i:indt-decl, o:indt-decl.
  bind-header [] Decl Bound :- copy-indt-decl Decl Bound.
  bind-header [binder Name Kind Ty Var | H] Decl (parameter Name Kind Domain Tail) :-
    copy Ty Domain, pi x\ (copy Var x :- !) => bind-header H Decl (Tail x).

  pred abstract-term i:list header-binder, i:term, o:term.
  abstract-term [] T Closed :- copy T Closed.
  abstract-term [binder Name _ Ty Var | H] T (fun N Domain Tail) :-
    coq.id->name Name N, copy Ty Domain,
    pi x\ (copy Var x :- !) => abstract-term H T (Tail x).

  pred parameter-levels i:list header-binder, o:list univ.variable.
  parameter-levels H Levels :-
    abstract-term H {{ Prop }} T, coq.univ.variable.of-term T Set,
    coq.univ.variable.set.elements Set All,
    std.filter All (l\ sigma u\ coq.univ.variable u l, not (coq.univ.global? u)) Levels.

  pred merge-levels i:list univ.variable, i:list univ.variable, o:list univ.variable.
  merge-levels First Rest Levels :-
    std.filter Rest (l\ not (std.mem First l)) New, std.append First New Levels.

  pred name-products i:list header-binder, i:term, o:term.
  name-products [] T T.
  name-products [binder N _ _ _ | H] (prod _ Ty Bo) (prod Name Ty Out) :-
    coq.id->name N Name, pi x\ name-products H (Bo x) (Out x).

  pred header-kinds i:list header-binder, o:list implicit_kind.
  header-kinds H Ks :- std.map H (b\k\ b = binder _ k _ _) Ks.

  pred set-header-kinds i:gref, i:list implicit_kind.
  set-header-kinds _ [] :- !.
  set-header-kinds Ref Ks :- @global! => coq.arguments.set-implicit Ref [Ks].

  pred declare-map i:id, i:term, o:constant.
  declare-map Name Term Ref :-
    local-header H, abstract-term H Term Closed,
    std.assert-ok! (coq.typecheck Closed Ty) ("Ill-typed map " ^ Name),
    name-products H Ty NamedTy, header-universes Levels,
    (@udecl! Levels tt [] tt => coq.env.add-const Name Closed NamedTy @transparent! Ref),
    set-header-kinds (const Ref) {header-kinds H}.

  % Anonymous definitions retain the declared parent applications at discharge.
  pred parent-type-in-scope i:inductive, o:term.
  pred parent-fields i:list inductive, i:list (pair id term), i:term, o:term.
  parent-fields [] _ Self Self.
  parent-fields [P | Ps] Env Self (let `_` Ty Value Tail) :-
    parent-type-in-scope P Ty, coq.safe-dest-app Ty Head Args,
    coq.env.indt P tt _ _ _ [K] _,
    if (Head = pglobal _ U) (@uinstance! U => coq.env.global (indc K) Ctor)
      (coq.env.global (indc K) Ctor),
    close P Cs, std.map Cs (c\t\ lookup {component-key c} Env t) Values,
    coq.mk-app Ctor {std.append Args Values} Value,
    pi x\ parent-fields Ps Env Self (Tail x).

  pred field-telescope i:list inductive, i:list component, i:record-decl,
      i:list (pair id term), i:term, o:term.
  field-telescope Ps [] end-record Env Self T :- parent-fields Ps Env Self T.
  field-telescope Ps [C | Cs] (field _ F Ty Rest) Env Self (prod Name Ty Tail) :-
    coq.id->name F Name, component-key C Key,
    pi x\ field-telescope Ps Cs (Rest x) [pr Key x | Env] Self (Tail x).

  pred declare-packed i:id, i:list inductive, i:list component, i:list (pair id id),
      o:inductive, o:list term.
  declare-packed N Parents Cs Names I Args :- @keep-alg-univs! ==>
    fields N Cs Names [] Body,
    {{ Set }} = sort Ground, field-sorts Body Ground Sort,
    Ctor is "Make" ^ N, Decl = inductive N tt (arity (sort Sort)) Constructors,
    (pi self\ sigma ty\ field-telescope Parents Cs Body [] self ty,
      Constructors self = [constructor Ctor (arity ty)]),
    local-header H, std.map H (b\x\ b = binder _ _ _ x) Args,
    if (H = []) (Bound = Decl) (bind-header H Decl Bound),
    std.assert-ok! (coq.typecheck-indt-decl Bound) ("Ill-typed structure " ^ N),
    if (struct-universes (upoly-decl Vs LV Cs0 LC))
      (if (LV = tt) (header-universes Ordered) (Ordered = Vs),
       @udecl! Ordered LV Cs0 LC => minks.add-record Bound I)
      (layout-levels Cs Body Levels, @udecl! Levels tt [] tt => minks.add-record Bound I),
    if (H = []) true (
      header-kinds H Kinds,
      minks.stored-projections I Projections,
      std.forall Projections (p\ @global! => coq.arguments.set-implicit p [Kinds])).

  pred generate-views i:id, i:list inductive, i:list component, i:inductive,
      o:list struct-conversion, o:list constant.
  generate-views N Parents Cs I Views Packers :-
    family-global (indt I) ChildTy,
    std.map Cs component-key Keys, stored-fields I Keys Fields,
    std.forall Cs (register-field 1 Cs Fields),
    std.assert! (ancestors Parents [] Reversed) "Could not read the ancestors",
    std.rev Reversed Ancestors,
    std.map Ancestors
      (p\v\ std.assert! (parent-view I ChildTy Fields Cs Parents p v)
        "Could not generate an ancestor view") ParentViews,
    std.map-filter Cs (c\v\ sigma key base proj\
      c = slot key (native-kind (ref-head (indt base))) _, std.mem Fields (pr key proj),
      v = conversion I base proj coercion-view) BaseViews,
    std.append ParentViews BaseViews Declared,
    discover-views I Cs Fields Declared OtherViews,
    std.append Declared OtherViews Views,
    std.forall ParentViews register-parent-view,
    std.filter Ancestors (p\ std.mem Parents p) DirectParents,
    std.map DirectParents (p\f\ pack-from-parent N I Cs p f) Packers.
}}.
