From elpi Require Import elpi.
From Minks Require Import
  Spec
  Flat.

(** * Relative interfaces

    Fix a dependency-closed selection of components as parameters.
    The remaining components become fields of a generated class. *)

Elpi File minks.relative lp:{{
  pred distinct-selection i:list id.
  distinct-selection [].
  distinct-selection [Key | Keys] :-
    if (std.mem Keys Key)
      (coq.error "Repeated export selection:" Key) true,
    distinct-selection Keys.

  % Declared ancestors already have instantiated inputs and child field names.
  % For an independent base use the same alignment as structural views.
  pred with-export-base i:inductive, i:list component, i:option inductive,
      i:(list component -> prop).
  with-export-base _ _ none K :- K [].
  with-export-base _ _ (some Base) K :-
    parent-inputs Base _, !, close Base Covered, K Covered.
  with-export-base Child Cs (some Base) K :-
    std.map Cs component-key Names, stored-fields Child Names Fields,
    struct-spec Base _ TargetCs,
    if (match-layout Child Cs Fields Base TargetCs Keys Indices) true
      (coq.error "Export base is not a substructure:" Base),
    active-family Child Args,
    std.map Indices (parameter-term Args) Inputs,
    std.map Keys (k\c\ std.mem Cs c, component-key c k) Covered,
    parent-inputs Base Inputs => K Covered.

  pred export-selection i:list component, i:list id, o:option inductive, o:list id.
  export-selection Cs Selection Base Keys :-
    distinct-selection Selection,
    std.map Cs component-key Available,
    std.partition Selection (k\ std.mem Available k) Keys Packed,
    if (Packed = []) (Base = none) (
      if (Packed = [Name]) true
        (coq.error "Expected at most one packed export base:" Packed),
      if (coq.locate-all Name [_ | _], coq.locate Name (indt I), spec I _ _) true
        (coq.error "Unknown export parameter key or packed structure:" Name),
      Base = some I).

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
    std.filter AllFixed (c\ not (contains-key {component-key c} Covered)) Fixed.

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
      (local-header H, header-global (const View) Head,
       std.map H (b\x\ b = binder _ _ _ x) Args, coq.mk-app Head {std.append Args [X]} T)
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

  % A relative class retains the header binders used by its signature,
  % including dependencies of the selected binder types.
  pred used-header i:list header-binder, i:indt-decl, o:list header-binder.
  used-header [] _ [].
  used-header [B | H] Decl Out :-
    B = binder _ _ _ X, used-header H Decl Rest,
    if (occurs X Decl ; std.exists Rest (b\ sigma ty\ b = binder _ _ ty _, occurs X ty))
      (Out = [B | Rest]) (Out = Rest).

  pred declare-relative i:id, i:option inductive, i:list component,
      i:list component, i:list component, i:list component,
      o:inductive, o:list (pair id constant), o:list term.
  declare-relative Name Base Covered Cs Fixed Remaining Export Refs Args :-
    relative-declaration Name Base Covered Fixed Remaining Open,
    local-header H, used-header H Open Needed, bind-header Needed Open Decl,
    std.map Needed (b\x\ b = binder _ _ _ x) Args,
    std.assert-ok! (coq.typecheck-indt-decl Decl)
      ("Ill-typed relative interface " ^ Name),
    header-universes Prefix, merge-levels Prefix {binder-levels Open} Levels,
    (@udecl! Levels tt [] tt => add-generated-record Decl Export),
    coq.TC.declare-class (indt Export),
    coq.env.projections Export Projections,
    std.map Remaining component-key RemainingKeys,
    std.map2 RemainingKeys Projections field-ref Refs,
    std.map Fixed (c\k\ k = maximal) Implicits,
    if (Base = none) (All = Implicits) (All = [maximal | Implicits]),
    std.append {header-kinds Needed} All Kinds,
    std.forall Refs (r\ sigma key p\
      r = pr key p, relative-projection Kinds p),
    std.forall Remaining (register-field 2 Cs Refs).

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
    family-global (indt Export) Class,
    coq.env.indt I tt _ _ _ [K] _, family-global (indc K) Ctor,
    pack-base Base Covered (args\bindings\t\
      pack-components Fixed bindings
        (env\body\ from-relative-body Class Ctor FixedKeys Keys Refs args env body) t) Term,
    declare-map Name Term _.

  pred generate-relative i:id, i:inductive, i:list component,
      i:list inductive, i:list struct-conversion, i:id, i:list id,
      o:inductive, o:list id.
  generate-relative Child I Cs Parents Views Name Selection Export Parameters :-
    export-selection Cs Selection Base Selected,
    with-export-base I Cs Base (covered\
      emit-relative Child I Cs Parents Views Name Base covered Selected Export Parameters).

  pred emit-relative i:id, i:inductive, i:list component, i:list inductive,
      i:list struct-conversion, i:id, i:option inductive, i:list component, i:list id,
      o:inductive, o:list id.
  emit-relative Child I Cs Parents Views Name Base Covered Selected Export Parameters :-
    std.forall Selected (k\
      if (contains-key k Covered)
        (coq.error "Export key is already supplied by the packed base:" k) true),
    relative-layout Cs Covered Selected Fixed Remaining,
    if (Remaining = []) (coq.error "No components remain to export:" Name) true,
    declare-relative Name Base Covered Cs Fixed Remaining Export Refs Args,
    active-family Export Args => (
      std.map Fixed component-key FixedKeys,
      std.map Remaining component-key RemainingKeys,
      std.append FixedKeys RemainingKeys ConstructorKeys,
      std.map Cs component-key Keys,
      stored-fields I Keys ChildRefs,
      std.map ConstructorKeys (k\t\ read-field ChildRefs k t) FromChild,
      coq.env.indt Export tt _ _ _ [Ctor] _,
      if (std.forall Remaining (auto-instance Cs))
        (std.map Refs (r\p\ sigma c\ r = pr _ c, p = const c) Projections,
         minks.cut-assembly Projections (indc Ctor),
         coq.TC.declare-instance (indc Ctor) 3)
        true,
      if (Base = some B)
        (coq.gref->id (indt B) BaseName, Parameters = [BaseName | FixedKeys])
        (Parameters = FixedKeys),
      std.map RemainingKeys (k\p\ std.mem ChildRefs (pr k p)) Origins,
      Layout = relative-interface Base Fixed Remaining Ctor Origins,
      coq.elpi.accumulate execution-site "minks.flat.db"
        (clause _ _ (declared (indt Export) (relative Layout))),
      family-global (indc Ctor) MakeExport,
      family-global (indt I) ChildTy,
      (pi x\ sigma bases args\
        relative-source Base Covered Views ChildRefs x bases,
        apply-fields FromChild x args,
        coq.mk-app MakeExport {std.append bases args} (Read x)),
      declare-view Child ChildTy Export Read Extraction,
      if (Fixed = [_ | _] ; Base = some Ancestor,
          ancestors Parents [] Ancestors, std.mem Ancestors Ancestor)
        (coq.TC.declare-instance (const Extraction) 1)
        true,
      PackName is Child ^ "Of" ^ Name,
      declare-relative-packer PackName Base Covered I Export Fixed FixedKeys Keys Refs).
}}.
