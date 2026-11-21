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
Elpi Accumulate File minks.spec.
Elpi Accumulate File minks.flat.
Elpi Accumulate Plugin "minks.combinations".
Elpi Accumulate File minks.relative.
Elpi Accumulate lp:{{
  pred usage.
  usage :-
    coq.error "Usage: Minks.Struct Name [extends Parent, ...]"
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

  pred parse-export-list i:list argument, o:list (pair id (list id)).
  parse-export-list [A | Args] [pr Name Keys | Rest] :-
    atom A Name,
    slot-deps Args Fixed Tail,
    if (Fixed = some Keys) true (Keys = []),
    (Tail = [], Rest = []
    ; Tail = [str "," | More], parse-export-list More Rest).

  pred parse-exports i:list argument, o:list (pair id (list id)).
  parse-exports [] [].
  parse-exports [str "exports" | Args] Exports :- parse-export-list Args Exports.

  pred resolve-parent i:id, o:inductive.
  resolve-parent Name I :-
    coq.locate Name Ref,
    if (Ref = indt I) true (coq.error "Expected a parent type:" Name).

  pred with-components i:list component, i:list (pair id term),
      i:(list (pair id term) -> prop).
  with-components [] Env Goal :- Goal Env.
  with-components [slot Key Ref Deps | Cs] Env Goal :-
    component-type Ref Deps Env Ty,
    std.assert-ok! (coq.typecheck-ty Ty _) ("Ill-typed inherited component " ^ Key),
    coq.id->name Key Name,
    pi x\ @pi-decl Name Ty x\ with-components Cs [pr Key x | Env] Goal.

  pred typecheck-arguments i:gref, i:list (pair id term), i:list id.
  typecheck-arguments Ref Env Deps :-
    component-type Ref Deps Env Ty,
    coq.typecheck-ty Ty _ ok.

  pred resolve-arguments i:id, i:gref, i:option (list id),
      i:list mixin-param, i:list component, i:list (pair id term), o:list id.
  resolve-arguments M Ref (some Keys) Params Available Env Keys :- !,
    if (mixin-arguments Params Available Env [] Keys,
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
  add-components [slot Key Ref Deps | Cs] Available Mapping Used
      Local [Actual | Args] Out :-
    std.map Deps (translate-key Mapping) ActualDeps,
    std.findall (match-component Key Ref ActualDeps Available Used _) Matches,
    std.map Matches (m\a\ m = match-component _ _ _ _ _ a) Keys,
    if (Keys = [Actual])
      (Local = New, Next = Available)
      (if (Keys = [])
        (Actual = Key,
         if (std.mem Used Key)
           (coq.error "An exported component key names a different selection:" Key) true,
         C = slot Key Ref ActualDeps, Local = [C | New], merge [C] Available Next)
        (coq.error "Ambiguous component for exported mixin:" Key Keys)),
    add-components Cs Next [pr Key Actual | Mapping] [Actual | Used] New Args Out.

  pred explicit-fixed i:list component, i:list id, i:list component,
      i:list (pair id id), i:list id.
  explicit-fixed [] [] _ _ _.
  explicit-fixed [slot Key Ref Deps | Cs] [Actual | Args] Available Mapping Used :-
    std.map Deps (translate-key Mapping) ActualDeps,
    std.mem Available (slot Actual Ref ActualDeps),
    not (std.mem Used Actual),
    explicit-fixed Cs Args Available [pr Key Actual | Mapping] [Actual | Used].

  pred resolve-fixed i:id, i:gref, i:option (list id), i:list component,
      i:list component, i:list (pair id term), o:list id.
  resolve-fixed M Ref (some Keys) Fixed Available Env Keys :- !,
    if (Keys = ["carrier" | Args],
        explicit-fixed Fixed Args Available [pr "carrier" "carrier"] ["carrier"],
        typecheck-arguments Ref Env Keys) true
      (coq.error "Component keys do not match the fixed export parameters:" M).
  resolve-fixed M Ref none Fixed Available Env ["carrier" | Args] :-
    std.findall (mapped-components Fixed Available [pr "carrier" "carrier"]
      ["carrier"] _) Candidates,
    std.map-filter Candidates
      (c\a\ c = mapped-components _ _ _ _ a,
        not (not (typecheck-arguments Ref Env ["carrier" | a]))) Matches,
    if (Matches = [Args]) true (
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
    if (Key = "carrier") (coq.error "Reserved component key:" Key) true,
    coq.locate M Ref,
    if (mixin-spec Ref _ Params) true
      (coq.error "Component must be a registered Minks mixin:" M),
    if (mixin-combination Ref Fixed Parts Ctor)
      (resolve-fixed M Ref Selection Fixed Available Env Deps,
       std.map Fixed component-key FixedKeys,
       assemble-components ["carrier" | FixedKeys] Deps Parts Available Additions Args Next,
       projection-name N Key Field Name,
       Views = [assembled Name Ctor Args | MoreViews], Names = MoreNames)
      (resolve-arguments M Ref Selection Params Available Env Deps,
       Component = slot Key Ref Deps, merge [Component] Available Next,
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
  avoid-view-name N Views Names (slot Key _ _) (pr Key Field) :-
    if (std.mem Names (pr Key Selected)) (Option = some Selected) (Option = none),
    projection-name N Key Option Default,
    if (std.exists Views (v\ assembled-name v Default))
      (if (Option = none) (Field is Default ^ "_component")
        (coq.error "Projection name is also used by an assembled view:" Default))
      (Field = Default).

  pred declare-assembled i:inductive, i:list (pair id constant), i:component-view,
      o:(pair constant (list id)).
  declare-assembled I Refs (assembled Name Ctor Keys) (pr Ref Keys) :-
    coq.env.global (indt I) Ty,
    coq.env.global (indc Ctor) Make,
    std.map Keys (k\t\ read-field Refs k t) Fields,
    view-body Make Fields Body,
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
    if (atom A Name, parse-parents Args ParentNames Rest,
        parse-components Rest Slots Tail, parse-exports Tail Exports) true usage,
    std.map ParentNames resolve-parent Parents,
    shared-carrier Parents Carrier,
    std.filter Parents (p\ spec p _ _) FlatParents,
    close-parents FlatParents Inherited,
    packed-carrier Carrier CarrierTy,
    (pi a\ @pi-decl `carrier` CarrierTy a\
      with-components Inherited [pr "carrier" a]
        (env\ resolve-slots Name Slots Inherited env Local Selected Assembled)),
    merge Local Inherited Components,
    if (Assembled = []) (Names = Selected)
      (std.map Components (avoid-view-name Name Assembled Selected) Names),
    std.assert! (generate Name FlatParents Components Names Carrier I Views Packers)
      "Could not generate the structure",
    if (Assembled = []) (Assemblies = []) (
      std.map Components component-key Keys,
      coq.env.projections I Projections,
      std.map2 ["carrier" | Keys] Projections field-ref Refs,
      std.map Assembled (declare-assembled I Refs) Assemblies),
    std.forall Views save-view,
    std.forall Packers (p\ coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (struct-packer I p))),
    if (Carrier = some Base)
      (coq.elpi.accumulate execution-site "minks.flat.db"
        (clause _ _ (fixed-carrier I Base))) true,
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (spec I FlatParents Local)),
    std.map Exports
      (e\v\ sigma label keys interface fixed layout\
        e = pr label keys, v = pr (pr interface fixed) layout,
        std.assert! (@keep-alg-univs! =>
          generate-relative Name I Carrier Components Views label keys interface fixed layout)
          ("Could not generate relative interface " ^ label),
        coq.elpi.accumulate execution-site "minks.flat.db"
          (clause _ _ (struct-export I interface fixed)))
      Entries,
    std.map Entries (e\v\ e = pr v _) Exported,
    std.map-filter Entries (e\l\ e = pr _ (some l)) Layouts,
    print-struct Name FlatParents Carrier Components Views Packers Exported Assemblies,
    discover-export-views Layouts.
  main _ :- usage.
}}.
Elpi Accumulate Db minks.flat.db.

Elpi Command minks.inspect.
Elpi Accumulate Db Header minks.flat.db.
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
    carrier-of I Carrier,
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
    print-struct Name Parents Carrier Cs Views Packers Exports Assemblies.

  main [str Name] :- !, coq.locate Name Ref, inspect Name Ref.
  main _ :- coq.error "Usage: Minks.Inspect Name.".
}}.
Elpi Accumulate Db minks.flat.db.
