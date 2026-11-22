From elpi Require Import elpi.
From Minks Require Import
  Spec
  Flat.

(** * Relative interfaces

    Fix a dependency-closed selection of components as parameters.
    The remaining components become fields of a generated class. *)

Elpi File minks.relative lp:{{
  kind export-layout type.
  type exported inductive -> list component -> list component -> constructor
    -> export-layout.
  pred distinct-selection i:list id.
  distinct-selection [].
  distinct-selection [Key | Keys] :-
    if (std.mem Keys Key)
      (coq.error "Repeated export selection:" Key) true,
    distinct-selection Keys.

  pred export-selection i:list component, i:list id,
      o:option inductive, o:list component, o:list id.
  export-selection Cs Selection Base Covered Keys :-
    distinct-selection Selection,
    std.map Cs component-key Available,
    std.partition Selection (k\ std.mem Available k) Keys Packed,
    if (Packed = []) (Base = none, Covered = []) (
      if (Packed = [Name]) true
        (coq.error "Expected at most one packed export base:" Packed),
      if (coq.locate-all Name [_ | _], coq.locate Name (indt I), spec I _ _) true
        (coq.error "Unknown export parameter key or packed structure:" Name),
      close I Covered,
      if (std.forall Covered (c\ std.mem Cs c)) true
        (coq.error "Export base is not a substructure:" Name),
      Base = some I,
      std.map Covered component-key CoveredKeys,
      std.forall Keys (k\
        if (std.mem CoveredKeys k)
          (coq.error "Export key is already supplied by the packed base:" k)
          true)).

  pred relative-layout i:list component, i:list component, i:list id,
      o:list component, o:list component.
  relative-layout Cs Covered Keys Fixed Remaining :-
    std.map Covered component-key CoveredKeys,
    std.rev Cs Reverse,
    std.fold Reverse {std.append Keys CoveredKeys} (c\seen\out\
      sigma key deps roots\
        c = slot key _ deps,
        if (std.mem seen key)
          (std.map deps input-keys roots, std.append {std.flatten roots} seen out)
          (out = seen))
      Closure,
    std.partition Cs (c\ std.mem Closure {component-key c}) AllFixed Remaining,
    std.filter AllFixed (c\ not (std.mem Covered c)) Fixed.

  % A named packed base supplies one binder and its constituent projections.
  pred base-bindings i:inductive, i:list component, i:term, o:list (pair id term).
  base-bindings Base Covered X Env :-
    std.map Covered component-key Keys, record-fields Base Keys Fields,
    apply-fields Fields X Args, std.map2 Keys Args (k\t\b\ b = pr k t) Env.

  pred relative-source i:option inductive, i:list component, i:list struct-conversion,
      i:list (pair id constant), i:term, o:list term.
  relative-source none _ _ _ _ [].
  relative-source (some Base) Covered Views Refs X [T] :-
    if (std.mem Views (conversion _ Base View _))
      (coq.env.global (const View) Head, coq.mk-app Head [X] T)
      (flat-view-body Refs Base Covered Body, T = Body X).

  pred relative-record i:id, i:list component, i:list component,
      i:list (pair id term), o:indt-decl.
  relative-record Name [] Remaining Env (record Name (sort Sort) Ctor Body) :-
    Ctor is "Make" ^ Name,
    fields Name Remaining [] Env Body,
    field-sorts Body prop Sort.
  relative-record Name [C | Fixed] Remaining Env
      (parameter Key explicit Ty Tail) :-
    component-key C Key, field-type C Env Ty,
    pi x\ @pi-parameter Key Ty x\
      relative-record Name Fixed Remaining [pr Key x | Env] (Tail x).

  pred relative-projection i:list implicit_kind, i:constant.
  relative-projection Implicits Projection :-
    @global! => coq.arguments.set-implicit (const Projection) [Implicits].

  pred relative-declaration i:id, i:option inductive, i:list component,
      i:list component, i:list component, o:indt-decl.
  relative-declaration Name none _ Fixed Remaining Decl :-
    relative-record Name Fixed Remaining [] Decl.
  relative-declaration Name (some Base) Covered Fixed Remaining
      (parameter "base" explicit Ty Tail) :-
    parent-global Base (indt Base) Ty,
    pi x\ @pi-parameter "base" Ty x\
      relative-record Name Fixed Remaining {base-bindings Base Covered x} (Tail x).

  pred binder-levels i:indt-decl, o:list univ.variable.
  binder-levels (parameter _ _ Ty _) Levels :- !, head-levels Ty Levels.
  binder-levels _ [].

  pred declare-relative i:id, i:option inductive, i:list component,
      i:list component, i:list component, i:list component,
      o:inductive, o:list (pair id constant).
  declare-relative Name Base Covered Cs Fixed Remaining Export Refs :-
    relative-declaration Name Base Covered Fixed Remaining Decl,
    std.assert-ok! (coq.typecheck-indt-decl Decl)
      ("Ill-typed relative interface " ^ Name),
    binder-levels Decl Levels,
    (@udecl! Levels tt [] tt => coq.env.add-indt Decl Export),
    coq.TC.declare-class (indt Export),
    coq.env.projections Export Projections,
    std.map Remaining component-key RemainingKeys,
    std.map2 RemainingKeys Projections field-ref Refs,
    std.map Fixed (c\k\ k = maximal) Implicits,
    if (Base = none) (All = Implicits) (All = [maximal | Implicits]),
    std.forall Refs (r\ sigma key p\
      r = pr key p, relative-projection All p),
    std.forall Remaining (register-field Cs Refs tt).

  pred from-relative-body i:term, i:term, i:list id, i:list id,
      i:list (pair id constant), i:list term, i:list (pair id term), o:term.
  from-relative-body Class Ctor FixedKeys Keys Refs Base Env (fun `view` ViewTy Body) :-
    std.map FixedKeys (k\t\ lookup k Env t) FixedArgs,
    std.append Base FixedArgs Args,
    coq.mk-app Class Args ViewTy,
    (pi v\ sigma inputs\
      std.map Keys (k\t\ sigma proj\
        if (std.mem Env (pr k t)) true
          (read-field Refs k proj, coq.mk-app proj {std.append Args [v]} t)) inputs,
      coq.mk-app Ctor inputs (Body v)).

  pred pack-base i:option inductive, i:list component,
      i:(list term -> list (pair id term) -> term -> prop), o:term.
  pack-base none _ Build Term :- Build [] [] Term.
  pack-base (some Base) Covered Build (fun `base` Ty Body) :-
    parent-global Base (indt Base) Ty,
    pi x\ Build [x] {base-bindings Base Covered x} (Body x).

  pred declare-relative-packer i:id, i:option inductive, i:list component,
      i:inductive, i:inductive, i:list component, i:list id, i:list id,
      i:list (pair id constant).
  declare-relative-packer Name Base Covered I Export Fixed FixedKeys Keys Refs :-
    coq.env.global (indt Export) Class,
    coq.env.indt I tt 0 0 _ [K] _, coq.env.global (indc K) Ctor,
    pack-base Base Covered (args\bindings\t\
      pack-components Fixed bindings
        (env\body\ from-relative-body Class Ctor FixedKeys Keys Refs args env body) t) Term,
    std.assert-ok! (coq.typecheck Term Ty) ("Ill-typed packing function " ^ Name),
    @univpoly! => coq.env.add-const Name Term Ty @transparent! _.

  pred register-relative i:option inductive, i:inductive, i:constructor,
      i:list component, i:list component, i:list id, o:list id.
  register-relative Base Export Ctor Fixed Remaining FixedKeys Parameters :-
    if (Base = some I)
      (coq.gref->id (indt I) Name, Parameters = [Name | FixedKeys],
       coq.elpi.accumulate execution-site "minks.flat.db"
         (clause _ _ (export-base (indt Export) I)))
      (Parameters = FixedKeys),
    std.length Parameters Arity,
    std.map Remaining component-key Keys,
    std.map-filter Remaining (c\k\ c = slot k (native-kind _) _) Ordinary,
    minks.register-combination Export (indc Ctor) Arity Keys Ordinary,
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (mixin-combination (indt Export) Fixed Remaining Ctor)).

  pred export-view-term i:inductive, i:list component, i:list component,
      i:constructor, i:list id, o:term.
  export-view-term Source Fixed Remaining TargetCtor Selected Term :-
    coq.env.global (indt Source) SourceTy,
    coq.env.global (indc TargetCtor) MakeTarget,
    std.map Fixed component-key FixedKeys,
    std.map Remaining component-key StoredKeys,
    coq.env.projections Source Projections,
    std.map2 StoredKeys Projections field-ref Refs,
    pack-components Fixed []
      (env\body\ sigma args source-type result\
        std.map FixedKeys (k\t\ lookup k env t) args,
        coq.mk-app SourceTy args source-type,
        body = fun `source` source-type result,
        pi source\ sigma all-args fields selected\
          all-args = {std.append args [source]},
          std.map Refs (r\f\ sigma key ref head value\
            r = pr key ref, f = pr key value,
            coq.env.global (const ref) head, coq.mk-app head all-args value) fields,
          std.map Selected (k\t\ lookup k {std.append env fields} t) selected,
          coq.mk-app MakeTarget selected (result source)) Term.

  pred infer-export-view i:export-layout, i:export-layout, o:struct-conversion.
  infer-export-view (exported Source SF SR _) (exported Target TF TR Ctor)
      (conversion Source Target View explicit-view) :-
    SourceCs = {std.append SF SR},
    TargetCs = {std.append TF TR},
    std.length TargetCs N,
    std.length SourceCs M,
    N < M,
    not (struct-view Source Target _ _),
    std.findall (mapped-components TargetCs SourceCs [] [] _) [mapped-components _ _ _ _ Selected],
    coq.gref->id (indt Source) From,
    view-name From Target Name,
    coq.env.current-path Here,
    std.string.concat "." {std.append Here [Name]} Qualified,
    coq.locate-all Qualified [],
    export-view-term Source SF SR Ctor Selected Term,
    coq.typecheck Term Ty ok,
    (@univpoly! => coq.env.add-const Name Term Ty @transparent! View),
    std.map SF (c\k\ k = maximal) Implicits,
    relative-projection Implicits View,
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (struct-view Source Target View explicit-view)).

  pred remember-export-views i:export-layout, i:list export-layout, o:list export-layout.
  remember-export-views New Previous [New | Previous] :-
    std.forall Previous (old\ sigma outgoing incoming\
      if (infer-export-view New old outgoing) (print-view outgoing) true,
      if (infer-export-view old New incoming) (print-view incoming) true).

  pred discover-export-views i:list export-layout.
  discover-export-views [] :- !.
  discover-export-views Layouts :-
    std.findall (mixin-combination _ _ _ _) Stored,
    std.map-filter Stored (m\l\ sigma i fixed remaining ctor\
      m = mixin-combination (indt i) fixed remaining ctor,
      not (export-base (indt i) _), l = exported i fixed remaining ctor) Previous,
    std.fold Layouts Previous remember-export-views _.

  pred generate-relative i:id, i:inductive, i:list component,
      i:list struct-conversion, i:id, i:list id, o:inductive, o:list id,
      o:option export-layout.
  generate-relative Child I Cs Views Name Selection Export Parameters Layout :-
    export-selection Cs Selection Base Covered Selected,
    relative-layout Cs Covered Selected Fixed Remaining,
    declare-relative Name Base Covered Cs Fixed Remaining Export Refs,
    std.map Fixed component-key FixedKeys,
    std.map Remaining component-key RemainingKeys,
    std.append FixedKeys RemainingKeys ConstructorKeys,
    std.map Cs component-key Keys,
    coq.env.projections I ChildProjections,
    std.map2 Keys ChildProjections field-ref ChildRefs,
    std.map ConstructorKeys (k\t\ read-field ChildRefs k t) FromChild,
    coq.env.indt Export tt _ _ _ [Ctor] _,
    register-relative Base Export Ctor Fixed Remaining FixedKeys Parameters,
    if (Base = none) (Layout = some (exported Export Fixed Remaining Ctor))
      (Layout = none),
    coq.env.global (indc Ctor) MakeExport,
    coq.env.global (indt I) ChildTy,
    (pi x\ sigma bases args\
      relative-source Base Covered Views ChildRefs x bases,
      apply-fields FromChild x args,
      coq.mk-app MakeExport {std.append bases args} (Read x)),
    declare-view Child ChildTy Export Read _,
    PackName is Child ^ "Of" ^ Name,
    declare-relative-packer PackName Base Covered I Export Fixed FixedKeys Keys Refs.
}}.
