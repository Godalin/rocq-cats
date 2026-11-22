From elpi Require Import elpi.
From Minks Require Import
  Mixin
  Spec
  Flat
  Relative.

(** * Declare and inspect structures

    Declarations combine previously generated parents with new mixins.
    Inspection explains the component choices used by the generator. *)

Elpi Command minks.struct.
Elpi Accumulate Db Header minks.flat.db.
Elpi Accumulate Plugin "minks.combinations".
Elpi Accumulate File minks.spec.
Elpi Accumulate File minks.flat.
Elpi Accumulate File minks.relative.
Elpi Accumulate lp:{{
  pred usage.
  usage :-
    coq.error "Usage: Minks.Struct Name [extends Parent arg ..., ...]"
      "[with key : Mixin [dependency, ...], ...]"
      "[exports Interface [key, ...], ...].".

  pred parse-deps i:list argument, o:list id, o:list argument.
  parse-deps [str "[", str "]" | Rest] [] Rest :- !.
  parse-deps [str "[" | Rest] Deps Tail :- ids Rest Deps [str "]" | Tail].

  kind pending-slot type.
  type pending id -> id -> option (list id) -> option id -> pending-slot.

  pred slot-deps i:list argument, o:option (list id), o:list argument.
  slot-deps [str "[" | Rest] (some Keys) Tail :- !,
    parse-deps [str "[" | Rest] Keys Tail.
  slot-deps Args none Args.

  pred parse-slot i:list argument, o:pending-slot, o:list argument.
  parse-slot [A, str "as", F, str ":", B | Rest]
      (pending Key M Deps (some Field)) Tail :- !,
    atom A Key, atom F Field, atom B M, slot-deps Rest Deps Tail.
  parse-slot [A, str ":", B | Rest] (pending Key M Deps none) Tail :-
    atom A Key, atom B M, slot-deps Rest Deps Tail.

  pred parse-slots i:list argument, o:list pending-slot, o:list argument.
  parse-slots Args [Slot | Slots] Rest :-
    parse-slot Args Slot Tail,
    if (Tail = [str "," | More]) (parse-slots More Slots Rest)
      (Slots = [], Rest = Tail).

  pred parse-components i:list argument, o:list pending-slot, o:list argument.
  parse-components [str "with" | Rest] Slots Tail :- !, parse-slots Rest Slots Tail.
  parse-components Rest [] Rest.

  pred parse-export-list i:list argument, o:list (pair id (option (list id))).
  parse-export-list [A | Args] [pr Name Keys | Rest] :-
    atom A Name,
    slot-deps Args Keys Tail,
    (Tail = [], Rest = []
    ; Tail = [str "," | More], parse-export-list More Rest).

  pred parse-exports i:list argument, o:list (pair id (option (list id))).
  parse-exports [] [].
  parse-exports [str "exports" | Args] Exports :- parse-export-list Args Exports.

  pred resolve-parent i:id, i:list id, o:struct-parent.
  resolve-parent "Type" [] (native-parent sort-head []) :- !.
  resolve-parent Name Args Parent :-
    coq.locate Name Ref,
    if (Ref = indt I, struct-spec I _ _) (Parent = named-parent I Args)
      (Parent = native-parent (ref-head Ref) Args).

  pred parent-args i:list argument, o:list id, o:list argument.
  parent-args [A | As] [Name | Names] Tail :- atom A Name, !,
    parent-args As Names Tail.
  parent-args As [] As.

  pred applications i:list argument, o:list struct-parent, o:list argument.
  applications [A | As] [Parent | Parents] Tail :-
    atom A Name, parent-args As Args Rest, resolve-parent Name Args Parent,
    if (Rest = [str "," | More]) (applications More Parents Tail)
      (Parents = [], Rest = Tail).

  pred struct-parents i:list argument, o:list struct-parent, o:list argument.
  struct-parents [str "extends" | As] Parents Rest :- !, applications As Parents Rest.
  struct-parents As [] As.

  pred section-name i:term, o:id.
  section-name (global (const C)) Name :-
    coq.env.section-variables Vars, std.mem Vars C, coq.gref->id (const C) Name.

  % The native view has already undergone all enclosing Section discharges.
  pred ancestor-inputs i:inductive, i:list term, i:inductive,
      o:(pair inductive (list id)).
  ancestor-inputs I Args Parent (pr Parent Names) :-
    struct-view I Parent C _, coq.env.global (const C) View,
    coq.mk-app View Args Applied, coq.typecheck Applied (prod _ _ Body) ok,
    pi child\ sigma head terms\ coq.safe-dest-app (Body child) head terms,
      std.map terms section-name Names.

  pred scope-parents i:list (pair inductive (list id)), i:prop.
  scope-parents [] Goal :- Goal.
  scope-parents [pr I Names | Rest] Goal :-
    spec I Parents _,
    coq.env.indt I tt Arity _ _ [K] _,
       if (std.length Names Arity) true
         (coq.error "Wrong number of structure parent parameters:" I Names),
       std.map Names (n\p\ sigma k t\
         if (section-input n k t) (p = pr k t)
           (coq.error "Unknown structure parent parameter:" n)) Inputs,
       std.map Inputs (p\k\ p = pr k _) Keys, std.map Inputs (p\t\ p = pr _ t) Args,
       if (parent-inputs I Prior _)
         (if (Keys = Prior) (scope-parents Rest Goal)
           (coq.error "Incompatible applications of a shared structure parent:" I))
         (coq.env.global (indt I) Head, coq.mk-app Head Args Ty,
          std.assert-ok! (coq.typecheck-ty Ty _) "Ill-typed structure parent application",
          close I Cs, coq.env.typeof (indc K) CtorTy,
          specialize-layout CtorTy Keys [] Cs Layout,
          std.map Parents (ancestor-inputs I Args) More,
          parent-inputs I Keys Args => parent-components I Layout =>
            scope-parents {std.append More Rest} Goal).

  pred with-components i:list component, i:list (pair id term),
      i:(list (pair id term) -> prop).
  with-components [] Env Goal :- Goal Env.
  with-components [C | Cs] Env Goal :-
    component-key C Key, field-type C Env Ty,
    std.assert-ok! (coq.typecheck-ty Ty _) ("Ill-typed inherited component " ^ Key),
    coq.id->name Key Name,
    pi x\ @pi-decl Name Ty x\ with-components Cs [pr Key x | Env] Goal.

  pred typecheck-arguments i:gref, i:list (pair id term), i:list id.
  typecheck-arguments Ref Env Deps :-
    component-type Ref Deps Env Ty,
    coq.typecheck-ty Ty _ ok.

  pred resolve-arguments i:id, i:gref, i:option (list id),
      i:list mixin-param, i:list component, i:list (pair id term), o:list id.
  resolve-arguments M Ref (some Names) Params Available Env Keys :- !,
    std.map Names (explicit-input Env) Keys,
    std.map-filter Keys (k\p\ sigma t\ ambient-value k t, p = pr k t) Inputs,
    if (mixin-arguments Params Available {std.append Inputs Env} [] Keys,
        typecheck-arguments Ref Env Keys) true
      (coq.error "Component keys do not match the mixin parameters:" M).
  resolve-arguments M Ref none Params Available Env Deps :-
    std.findall (mixin-arguments Params Available Env [] _) Candidates,
    % Keep candidate typing inside the local universe context and discard
    % its constraints before checking the next candidate.
    std.map-filter Candidates
      (candidate\keys\ candidate = mixin-arguments _ _ _ _ keys,
        not (not (typecheck-arguments Ref Env keys))) Matches,
    if (Matches = [Deps]) true (
      if (Matches = [])
        (coq.error "Missing compatible arguments for mixin:" M)
        (coq.error "Ambiguous arguments for mixin, give component keys:" M)).

  kind component-view type.
  type assembled id -> constructor -> list id -> component-view.

  pred add-components i:list component, i:list component,
      i:list (pair id id), i:list id, o:list component, o:list id, o:list component.
  add-components [] Available _ _ [] [] Available.
  add-components [Field | Cs] Available Mapping Used
      Local [Actual | Args] Out :-
    Field = slot Key Kind Deps,
    std.map Deps (translate-key Mapping) ActualDeps,
    std.findall (match-component Key Kind ActualDeps Available Used _) Matches,
    std.map Matches (m\a\ m = match-component _ _ _ _ _ a) Keys,
    if (Keys = [Actual])
      (Local = New, Next = Available)
      (if (Keys = [])
        (Actual = Key,
         if (std.mem Used Key)
           (coq.error "An exported component key names a different selection:" Key) true,
         C = slot Key Kind ActualDeps, Local = [C | New], merge [C] Available Next)
        (coq.error "Ambiguous component for exported mixin:" Key Keys)),
    add-components Cs Next [pr Key Actual | Mapping] [Actual | Used] New Args Out.

  pred explicit-fixed i:list component, i:list id, i:list component,
      i:list (pair id id), i:list id.
  explicit-fixed [] [] _ _ _.
  explicit-fixed [C | Cs] [Actual | Args] Available Mapping Used :-
    C = slot Key Kind Deps, std.map Deps (translate-key Mapping) ActualDeps,
    std.mem Available (slot Actual Kind ActualDeps),
    not (std.mem Used Actual),
    explicit-fixed Cs Args Available [pr Key Actual | Mapping] [Actual | Used].

  pred fixed-mapping i:list id, i:list id, o:list (pair id id).
  fixed-mapping Prefix Values Mapping :-
    std.map2 Prefix Values (k\v\p\ p = pr k v) Mapping.

  pred infer-fixed i:list id, i:list component, i:list component,
      i:list (pair id term), o:list id.
  infer-fixed Prefix Fixed Available Env Keys :-
    std.map Prefix (_\v\ std.mem Env (pr v _)) Values,
    fixed-mapping Prefix Values Mapping,
    mapped-components Fixed Available Mapping [] Args,
    std.append Values Args Keys.

  pred resolve-fixed i:id, i:gref, i:option (list id), i:list id, i:list component,
      i:list component, i:list (pair id term), o:list id.
  resolve-fixed M Ref (some Names) Prefix Fixed Available Env Keys :- !,
    std.map Names (explicit-input Env) Keys,
    std.length Prefix N,
    if (std.split-at N Keys Values Args,
        fixed-mapping Prefix Values Mapping,
        explicit-fixed Fixed Args Available Mapping [],
        typecheck-arguments Ref Env Keys) true
      (coq.error "Component keys do not match the fixed export parameters:" M).
  resolve-fixed M Ref none Prefix Fixed Available Env Keys :-
    std.findall (infer-fixed Prefix Fixed Available Env _) Candidates,
    std.map-filter Candidates
      (c\a\ c = infer-fixed _ _ _ _ a,
        not (not (typecheck-arguments Ref Env a))) Matches,
    if (Matches = [Keys]) true (
      if (Matches = [])
        (coq.error "Missing compatible arguments for exported mixin:" M)
        (coq.error "Ambiguous fixed parameters for exported mixin, give component keys:" M)).

  pred assemble-components i:list id, i:list id, i:list component,
      i:list component, o:list component, o:list id, o:list component.
  assemble-components Fixed ActualFixed Parts Available Local Args Out :-
    std.map2 Fixed ActualFixed (k\a\p\ p = pr k a) Mapping,
    std.findall (mapped-components Parts Available Mapping ActualFixed _) Matches,
    if (Matches = [Match])
      (Match = mapped-components _ _ _ _ Components, Local = [], Out = Available)
      (if (Matches = [])
        (add-components Parts Available Mapping ActualFixed Local Components Out)
        (coq.error "Ambiguous component selection for exported mixin:" Parts)),
    std.append ActualFixed Components Args.

  pred projection-name i:id, i:id, i:option id, o:id.
  projection-name N Key none Name :- field-name N Key Name.
  projection-name _ _ (some Name) Name.

  pred resolve-slots i:id, i:list pending-slot, i:list component,
      i:list (pair id term), o:list component, o:list (pair id id),
      o:list component-view.
  resolve-slots _ [] _ _ [] [] [].
  resolve-slots N [pending Key M Selection Field | Slots] Available Env
      Local Names Views :-
    coq.locate M Ref,
    if (mixin-spec Ref _ Params) true
      (coq.error "Component must be a registered Minks mixin:" M),
    if (mixin-combination Ref RawFixed RawParts Ctor)
      (Ref = indt Interface, std.length RawFixed F,
       current-layout Interface F {std.append RawFixed RawParts} Ordinary Layout,
       std.split-at F Layout Fixed Parts,
       std.map Ordinary parameter-key Prefix,
       resolve-fixed M Ref Selection Prefix Fixed Available Env Deps,
       std.map Fixed component-key FixedKeys,
       assemble-components {std.append Prefix FixedKeys} Deps Parts Available Additions Args Next,
       projection-name N Key Field Name,
       Views = [assembled Name Ctor Args | MoreViews], Names = MoreNames)
      (resolve-arguments M Ref Selection Params Available Env Deps,
       Component = slot Key (mixin-kind Ref) Deps, merge [Component] Available Next,
       if (std.mem Available Component) (Additions = []) (Additions = [Component]),
       Views = MoreViews,
       if (Field = some Name) (Names = [pr Key Name | MoreNames]) (Names = MoreNames)),
    std.append Additions Rest Local,
    with-components Additions Env (next-env\
      resolve-slots N Slots Next next-env Rest MoreNames MoreViews).

  pred assembled-name i:component-view, o:id.
  assembled-name (assembled Name _ _) Name.

  pred avoid-view-name i:id, i:list component-view, i:list (pair id id),
      i:component, o:(pair id id).
  avoid-view-name N Views Names C (pr Key Field) :-
    component-key C Key,
    if (std.mem Names (pr Key Selected)) (Option = some Selected) (Option = none),
    if (Option = some Explicit) (Default = Explicit) (projection-id N C Default),
    if (std.exists Views (v\ assembled-name v Default))
      (if (Option = none) (Field is Default ^ "_component")
        (coq.error "Projection name is also used by an assembled view:" Default))
      (Field = Default).

  pred declare-assembled i:inductive, i:list (pair id constant), i:component-view,
      o:(pair constant (list id)).
  declare-assembled I Refs (assembled Name Ctor Keys) (pr Ref Keys) :-
    coq.env.global (indt I) Ty,
    coq.env.global (indc Ctor) Make,
    (pi child\ sigma args\
      std.map Keys (k\t\ if (ambient-value k t) true
        (sigma proj\ read-field Refs k proj, coq.mk-app proj [child] t)) args,
      coq.mk-app Make args (Body child)),
    coq.id->name "structure" Binder,
    Term = fun Binder Ty Body,
    std.assert-ok! (coq.typecheck Term ViewTy) ("Ill-typed assembled view " ^ Name),
    (@univpoly! => coq.env.add-const Name Term ViewTy @transparent! Ref),
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (struct-assembly I Ref Keys)).

  pred save-view i:struct-conversion.
  save-view (conversion Source Target Ref Mode) :-
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (struct-view Source Target Ref Mode)).

  main [A | Args] :-
    if (atom A Name, struct-parents Args Applications Rest,
        parse-components Rest Slots Tail, parse-exports Tail Exports) true usage,
    resolve-bases Applications (parents\
      std.map parents (a\p\ sigma i args\ a = named-parent i args, p = pr i args) Named,
      scope-parents Named (build Name parents Slots Exports)).

  pred resolve-bases i:list struct-parent, i:(list struct-parent -> prop).
  resolve-bases [] K :- K [].
  resolve-bases [named-parent I Args | Ps] K :-
    resolve-bases Ps (rest\ K [named-parent I Args | rest]).
  resolve-bases [native-parent Head Args | Ps] K :-
    std.findall (native-base Head _) Known,
    Continue = (i\ resolve-bases Ps (rest\ K [named-parent i Args | rest])),
    if (Known = [native-base _ I]) (Continue I)
      (if (Known = []) (
         generate-base Head I Cs,
         Registration = native-base Head I, Signature = struct-spec I [] Cs,
         coq.elpi.accumulate execution-site "minks.flat.db" (clause _ _ Registration),
         coq.elpi.accumulate execution-site "minks.flat.db" (clause _ _ Signature),
         Registration => Signature => Continue I)
       (coq.error "Several visible bases for native parent; name the intended structure:" Head)).

  pred export-keys i:list (list component), i:list component, i:option (list id), o:list id.
  export-keys _ _ (some Keys) Keys.
  export-keys Parents Inherited none Keys :-
    std.filter Inherited (c\ std.forall Parents (p\ std.mem p c)) Common,
    std.map Common component-key Keys.

  pred build i:id, i:list struct-parent, i:list pending-slot, i:list (pair id (option (list id))).
  build Name Applications Slots Exports :-
    struct-ancestors Applications FlatParents,
    std.map Applications parent-layout Branches, close-parents Branches Inherited,
    with-components Inherited []
      (env\ resolve-slots Name Slots Inherited env Local Selected Assembled),
    merge Local Inherited Components,
    if (Assembled = []) (Names = Selected)
      (std.map Components (avoid-view-name Name Assembled Selected) Names),
    std.assert! (generate Name FlatParents Components Names I Views Packers)
      "Could not generate the structure",
    if (Assembled = []) (Assemblies = []) (
      std.map Components component-key Keys,
      coq.env.projections I Projections,
      std.map2 Keys Projections field-ref Refs,
      std.map Assembled (declare-assembled I Refs) Assemblies),
    std.forall Views save-view,
    std.forall Packers (p\ coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (struct-packer I p))),
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (struct-spec I Applications Components)),
    std.map Exports
      (e\v\ sigma label selection keys interface fixed layout\
        e = pr label selection, export-keys Branches Inherited selection keys, v = pr (pr interface fixed) layout,
        std.assert! (@keep-alg-univs! =>
          generate-relative Name I Components Views label keys interface fixed layout)
          ("Could not generate relative interface " ^ label),
        coq.elpi.accumulate execution-site "minks.flat.db"
          (clause _ _ (struct-export I interface fixed)))
      Entries,
    std.map Entries (e\v\ e = pr v _) Exported,
    std.map-filter Entries (e\l\ e = pr _ (some l)) Layouts,
    print-struct Applications Name [] FlatParents Components Views Packers Exported Assemblies,
    discover-export-views Layouts.
  main _ :- usage.
}}.
Elpi Accumulate Db minks.flat.db.

Elpi Command minks.inspect.
Elpi Accumulate Db Header minks.flat.db.
Elpi Accumulate Plugin "minks.combinations".
Elpi Accumulate File minks.spec.
Elpi Accumulate lp:{{
  pred inspect i:id, i:gref.
  inspect _ Ref :-
    packed-export Ref Base Fixed Remaining, !,
    print-packed-export Ref Base Fixed Remaining.
  inspect Name Ref :-
    mixin-spec Ref Direct Params, !,
    print-mixin Name Direct Params, print-combination Ref,
    if (Ref = indt I)
      (std.findall (struct-view I _ _ explicit-view) Stored,
       if (Stored = []) true (
         coq.say "Conversions:",
         std.forall Stored (v\ sigma target fn\
           v = struct-view I target fn explicit-view,
           print-view (conversion I target fn explicit-view))))
      true.
  inspect Name Ref :-
    if (Ref = indt I, spec I Parents _) true
      (coq.error "Not a Minks structure:" Name),
    close I Cs,
    std.findall (struct-view I _ _ _) Stored,
    std.map Stored
      (v\out\ sigma target ref mode\
        v = struct-view I target ref mode, out = conversion I target ref mode)
      Views,
    std.findall (struct-packer I _) StoredPackers,
    std.map StoredPackers (p\ref\ p = struct-packer I ref) Packers,
    std.findall (struct-export I _ _) StoredExports,
    std.map StoredExports
      (e\v\ sigma interface fixed\
        e = struct-export I interface fixed, v = pr interface fixed)
      Exports,
    std.findall (struct-assembly I _ _) StoredAssemblies,
    std.map StoredAssemblies (a\v\ sigma ref keys\
      a = struct-assembly I ref keys, v = pr ref keys) Assemblies,
    current-layout I 0 Cs Params Layout,
    struct-spec I Declared _,
    print-struct Declared Name Params Parents Layout Views Packers Exports Assemblies.

  main [str Name] :- !, coq.locate Name Ref, inspect Name Ref.
  main _ :- coq.error "Usage: Minks.Inspect Name.".
}}.
Elpi Accumulate Db minks.flat.db.
