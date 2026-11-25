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
      "[with key : Mixin | old as new | [keys] : Export, ...]"
      "[exports Interface [key, ...], ...].".

  pred parse-deps i:list argument, o:list id, o:list argument.
  parse-deps [str "[", str "]" | Rest] [] Rest :- !.
  parse-deps [str "[" | Rest] Deps Tail :- ids Rest Deps [str "]" | Tail].

  kind pending-slot type.
  type rename id -> id -> pending-slot.
  kind slot-binder type.
  type single id -> option id -> slot-binder.
  type batch option (list id) -> option (list id) -> slot-binder.
  type pending slot-binder -> term -> option (list id) -> pending-slot.

  pred slot-deps i:list argument, o:option (list id), o:list argument.
  slot-deps [str "[" | Rest] (some Keys) Tail :- !,
    parse-deps [str "[" | Rest] Keys Tail.
  slot-deps Args none Args.

  pred parse-slot i:list argument, o:pending-slot, o:list argument.
  parse-slot [A, str "as", F, str ":", trm M | Rest]
      (pending (single Key (some Field)) M Deps) Tail :- !,
    atom A Key, atom F Field, slot-deps Rest Deps Tail.
  parse-slot [A, str "as", F | Rest] (rename Key Name) Rest :-
    atom A Key, atom F Name, !.
  parse-slot [A, str ":", trm M | Rest] (pending (single Key none) M Deps) Tail :-
    atom A Key, !, slot-deps Rest Deps Tail.
  parse-slot Args (pending (batch Keys Aliases) M Deps) Tail :-
    slot-deps Args Keys After,
    if (After = [str "as" | More])
      (parse-deps More Names Rhs, Aliases = some Names) (Aliases = none, Rhs = After),
    Rhs = [str ":", trm M | Rest], slot-deps Rest Deps Tail.

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

  pred argument-label i:term, o:string.
  argument-label T Label :-
    coq.term->string T Text,
    if (coq.env.global _ T ; T = sort _) (Label = Text)
      (Label is "(" ^ Text ^ ")").

  % The command passes the whole application so Rocq elaborates dependent
  % arguments, implicit conversions and holes at their expected types.
  pred resolve-parent i:argument, o:struct-parent, o:term.
  resolve-parent (trm (sort (typ U))) (native-parent sort-head []) (sort (typ U)) :- !.
  resolve-parent (trm T) Parent T :-
    coq.safe-dest-app T Head Args, coq.env.global Ref Head,
    std.map Args argument-label Labels,
    if (Ref = indt I, struct-spec I _ _) (Parent = named-parent I Labels)
      (Parent = native-parent (ref-head Ref) Labels).

  pred applications i:list argument, o:list struct-parent, o:list term, o:list argument.
  applications [A | Rest] [Parent | Parents] [T | Terms] Tail :-
    resolve-parent A Parent T,
    if (Rest = [str "," | More]) (applications More Parents Terms Tail)
      (Parents = [], Terms = [], Rest = Tail).

  pred struct-parents i:list argument, o:list struct-parent, o:list term, o:list argument.
  struct-parents [str "extends" | As] Parents Args Rest :- !,
    applications As Parents Args Rest.
  struct-parents As [] [] As.

  % The wrapper's single field must have exactly the written native type.
  pred parent-type i:struct-parent, i:term, o:(pair inductive term).
  parent-type (named-parent I _) T (pr I T) :-
    coq.safe-dest-app T Head _, (Head = pglobal (indt I) _ ; Head = global (indt I)), !.
  parent-type (named-parent I _) T (pr I Ty) :-
    coq.safe-dest-app T _ Args, coq.env.indt I tt _ _ _ [K] _,
    coq.env.global (indc K) Make, coq.mk-app Make Args Applied,
    coq.typecheck Applied (prod _ Native Result) ok, coq.unify-eq Native T ok,
    pi x\ Ty = Result x.

  pred ancestor-type i:inductive, i:term, i:list term, i:inductive, o:(pair inductive term).
  ancestor-type I Ty Args Parent (pr Parent Result) :-
    struct-view I Parent C _, coq.env.global (const C) View,
    coq.mk-app View Args Applied, coq.typecheck Applied (prod _ Source Body) ok,
    coq.unify-eq Ty Source ok, pi x\ Result = Body x.

  % A field's global head carries the universe instance of this occurrence.
  pred scope-head i:id, i:field-kind, i:term, i:prop.
  scope-head Key Kind Head Goal :-
    if (selected-head Key Kind Prior)
      (std.assert-ok! (coq.unify-eq Head Prior) ("Incompatible field instances: " ^ Key), Goal)
      (selected-head Key Kind Head => Goal).

  pred layout-heads i:term, i:list component, o:list prop.
  layout-heads _ [] [].
  layout-heads (prod _ Ty Body) [slot Key Kind _ | Cs] [selected-head Key Kind Head | Hs] :-
    coq.safe-dest-app Ty Head _, pi x\ layout-heads (Body x) Cs Hs.

  pred with-heads i:list prop, i:prop.
  with-heads [] Goal :- Goal.
  with-heads [selected-head Key Kind Head | Hs] Goal :-
    scope-head Key Kind Head (with-heads Hs Goal).

  pred parent-telescope i:inductive, o:term.

  pred scope-parents i:list (pair inductive term), i:prop.
  scope-parents [] Goal :- Goal.
  scope-parents [pr I Ty | Rest] Goal :-
    spec I Parents _, coq.safe-dest-app Ty Head Args,
    if (parent-type-in-scope I Prior)
      (std.assert-ok! (coq.unify-eq Ty Prior) "Incompatible applications of a shared parent",
       scope-parents Rest Goal)
      (close I Cs, coq.env.indt I tt _ _ _ [K] _,
       if (Head = pglobal _ U) (@uinstance! U => coq.env.typeof (indc K) CtorTy)
         (coq.env.typeof (indc K) CtorTy),
       coq.subst-prod Args CtorTy FieldsTy, read-slots FieldsTy [] Cs Layout,
       std.map Parents (ancestor-type I Ty Args) More,
       parent-type-in-scope I Ty => parent-inputs I Args => parent-components I Layout =>
         parent-telescope I FieldsTy => scope-parents {std.append More Rest} Goal).

  pred with-components i:list component, i:list (pair id term),
      i:(list (pair id term) -> prop).
  with-components [] Env Goal :- (component-env Env :- !) => Goal Env.
  with-components [C | Cs] Env Goal :-
    component-key C Key, field-type C Env Ty,
    std.assert-ok! (coq.typecheck-ty Ty _) ("Ill-typed inherited component " ^ Key),
    coq.id->name Key Name,
    pi x\ @pi-decl Name Ty x\ with-components Cs [pr Key x | Env] Goal.

  pred typecheck-arguments i:term, i:list (pair id term), i:list id.
  typecheck-arguments Head Env Deps :-
    std.map Deps (k\t\ lookup k Env t) Args, coq.mk-app Head Args Ty,
    coq.typecheck-ty Ty _ ok.

  pred resolve-arguments i:id, i:term, i:option (list id),
      i:list mixin-param, i:list component, i:list (pair id term), o:list id.
  resolve-arguments M Head (some Keys) Params Available Env Keys :- !,
    std.map-filter Keys (k\p\ sigma t\ ambient-value k t, p = pr k t) Inputs,
    if (mixin-arguments Params Available {std.append Inputs Env} [] Keys,
        typecheck-arguments Head Env Keys) true
      (coq.error "Component keys do not match the mixin parameters:" M).
  resolve-arguments M Head none Params Available Env Deps :-
    std.findall (mixin-arguments Params Available Env [] _) Candidates,
    % Keep candidate typing inside the local universe context and discard
    % its constraints before checking the next candidate.
    std.map-filter Candidates
      (candidate\keys\ candidate = mixin-arguments _ _ _ _ keys,
        not (not (typecheck-arguments Head Env keys))) Matches,
    if (Matches = [Deps]) true (
      if (Matches = [])
        (coq.error "Missing compatible arguments for mixin:" M)
        (coq.error "Ambiguous arguments for mixin, give component keys:" M)).

  pred explicit-fixed i:list component, i:list id, i:list component,
      i:list (pair id id), i:list id.
  explicit-fixed [] [] _ _ _.
  explicit-fixed [C | Cs] [Actual | Args] Available Mapping Used :-
    C = slot Key Kind Deps, std.map Deps (translate-input Mapping) ActualDeps,
    (available-component Available Actual Kind ActualDeps ; ambient-value Actual _),
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

  pred resolve-fixed i:id, i:term, i:option (list id), i:list id, i:list component,
      i:list component, i:list (pair id term), o:list id.
  resolve-fixed M Head (some Keys) Prefix Fixed Available Env Keys :- !,
    std.length Prefix N,
    if (std.split-at N Keys Values Args,
        fixed-mapping Prefix Values Mapping,
        explicit-fixed Fixed Args Available Mapping [],
        typecheck-arguments Head Env Keys) true
      (coq.error "Component keys do not match the fixed export parameters:" M).
  resolve-fixed M Head none Prefix Fixed Available Env Keys :-
    std.findall (infer-fixed Prefix Fixed Available Env _) Candidates,
    std.map-filter Candidates
      (c\a\ c = infer-fixed _ _ _ _ a,
        not (not (typecheck-arguments Head Env a))) Matches,
    if (Matches = [Keys]) true (
      if (Matches = [])
        (coq.error "Missing compatible arguments for exported mixin:" M)
        (coq.error "Ambiguous fixed parameters for exported mixin, give component keys:" M)).

  % A parent keeps the identity of every field that it supplies. Only
  % matching native heads also admit their existing conversion check.
  pred parent-names i:struct-parent, o:list field-name-info.
  parent-names (named-parent I _) Names :-
    close I Cs, checked-field-names I Cs Stored,
    std.map Stored (r\n\ sigma k history origins\
      r = named-field k history origins,
      n = named-field k history [pr I k | origins]) Names.

  pred origin-projection i:inductive, i:id, o:gref.
  origin-projection I K (const P) :-
    struct-spec I _ Cs, std.map Cs component-key Keys,
    stored-fields I Keys Fields, std.mem Fields (pr K P).

  pred shares i:field-name-info, i:field-name-info.
  shares (named-field K H [pr I A | _]) (named-field J G [pr P B | _]) :-
    origin-projection I A Left, origin-projection P B Right,
    if (minks.same-key Left Right) true
      (K = J, H = [], G = [], struct-spec I _ Cs, struct-spec P _ Ds,
       std.mem Cs (slot A (native-kind _) _), std.mem Ds (slot B (native-kind _) _)).

  pred connected i:list field-name-info, i:list field-name-info, o:list field-name-info.
  connected Group Others Out :-
    std.partition Others (n\ std.exists Group (shares n)) More Rest,
    if (More = []) (Out = Group)
      (connected {std.append Group More} Rest Out).

  pred add-distinct i:list A, i:list A, o:list A.
  add-distinct Xs Acc Result :-
    std.fold Xs Acc (x\a\b\ if (std.mem a x) (b = a) (b = [x | a])) Result.

  pred merge-names i:list field-name-info, o:list field-name-info.
  merge-names [] [].
  merge-names [First | Rest] [named-field Key History Origins | Names] :-
    connected [First] Rest Group,
    std.partition [First | Rest] (n\ std.mem Group n) Ordered Others,
    if (std.mem Ordered (named-field Key [_ | _] _)) true
      (First = named-field Key _ _),
    std.fold Ordered [] (n\a\b\ sigma k h\ n = named-field k h _,
      add-distinct [k | h] a b) Spellings,
    std.filter Spellings (k\ not (k = Key)) History,
    std.fold Ordered [] (n\a\b\ sigma os\ n = named-field _ _ os,
      add-distinct os a b) Origins,
    merge-names Others Names,
    std.forall Spellings (k\ require-fresh Names k).

  pred require-fresh i:list field-name-info, i:id.
  require-fresh Names K :-
    if (std.mem Names (named-field K _ _) ; std.exists Names
        (n\ sigma h\ n = named-field _ h _, std.mem h K))
      (coq.error "Component key is already in use or retired:" K) true.

  pred rename-field i:list field-name-info, i:id, i:id, o:list field-name-info.
  rename-field [] K _ _ :- coq.error "No current field named" K.
  rename-field [named-field K H Os | Rest] K J [named-field J [K | H] Os | Rest] :- !.
  rename-field [F | Fs] K J [F | Rest] :- rename-field Fs K J Rest.

  pred entry-names i:slot-binder, i:term, o:list id, o:list (pair id id).
  entry-names Binder Head Keys Projections :-
    coq.env.global Ref Head,
    if (mixin-combination Ref _ _ Parts _ _)
      (if (Binder = batch Written Aliases) true
         (coq.error "Use an ordered list of keys to bind an exported mixin:" Ref),
       std.map Parts component-key Defaults,
       if (Written = some Ks) (std.map Ks (k\n\ binding-key k n _) Keys) (Keys = Defaults),
       std.assert! (std.length Keys {std.length Defaults}) "Wrong number of export keys",
       if (Aliases = some Ns)
         (std.assert! (fixed-mapping Keys Ns Projections) "Wrong number of projection names")
         (Projections = []))
      (if (Binder = single K Alias) true (coq.error "A primitive mixin needs one key:" Ref),
       binding-key K Short _, Keys = [Short],
       if (Alias = some P) (Projections = [pr Short P]) (Projections = [])).

  pred introduce-name i:id, i:list field-name-info, o:list field-name-info.
  introduce-name K Names [named-field K [] [] | Names] :- require-fresh Names K.

  % Before generating dependent types, validate each spelling in its source
  % scope. Then translate valid references to their final record keys.
  kind field-entry type.
  type entry list id -> list (pair id id) -> term -> option (list id)
    -> list (pair id id) -> field-entry.

  pred final-name i:list field-name-info, i:id, o:id.
  final-name Names K Key :-
    std.mem Names (named-field Key H _), (K = Key ; std.mem H K), !.

  pred resolve-spelling i:list field-name-info, i:list field-name-info, i:id, o:id.
  resolve-spelling Before Final K Actual :-
    if (std.mem Before (named-field K _ _))
      (if (ordinary-input K _ _) (coq.error "Both a parameter and a field have the name:" K)
         (final-name Final K Actual))
      (require-fresh Before K,
       if (ordinary-input K Ambient _) (Actual = Ambient)
         (coq.error "Unknown component input:" K)).

  pred plan-entries i:list pending-slot, i:list field-name-info,
      o:list field-name-info, o:list field-entry.
  plan-entries [] Names Names [].
  plan-entries [rename K J | Slots] Before Final Entries :-
    require-fresh Before J, rename-field Before K J After,
    plan-entries Slots After Final Entries.
  plan-entries [pending Binder Head Selection | Slots] Before Final
      [entry Out Aliases Head Deps Preferred | Entries] :-
    entry-names Binder Head Keys Ps,
    std.fold Keys Before introduce-name After,
    plan-entries Slots After Final Entries,
    % Original-key preference for omitted fixed inputs uses the spellings
    % visible here, including when a later entry renames one of them.
    if (Binder = batch _ _, Selection = none)
      (std.map Before (n\p\ sigma k\ n = named-field k _ _, p = pr k {final-name Final k}) Preferred)
      (Preferred = []),
    std.map Keys (final-name Final) Out,
    std.map Ps (p\q\ sigma k j\ p = pr k j, q = pr {final-name Final k} j) Aliases,
    if (Selection = some Ks)
      (std.map Ks (resolve-spelling Before Final) Values, Deps = some Values) (Deps = none).

  pred remap-component i:list (pair id id), i:component, o:component.
  remap-component Map (slot K Kind Ds) (slot J Kind Args) :-
    std.mem Map (pr K J), std.map Ds (translate-input Map) Args.

  pred scope-parent-keys i:list inductive, i:list field-name-info, i:prop.
  scope-parent-keys [] _ Goal :- Goal.
  scope-parent-keys [I | Is] Names Goal :-
    close I Cs,
    std.map Cs (c\p\ sigma k j os\ component-key c k,
      std.mem Names (named-field j _ os), std.mem os (pr I k), p = pr k j) Map,
    std.map Map (p\j\ p = pr _ j) Targets,
    distinct-selection Targets,
    std.map Cs (remap-component Map) Layout,
    parent-telescope I Ty, layout-heads Ty Layout Heads,
    (parent-components I Layout :- !) => with-heads Heads (scope-parent-keys Is Names Goal).

  pred expand-parts i:list component, i:list id, i:list (pair id id), o:list component.
  expand-parts [] [] _ [].
  expand-parts [slot K Kind Ds | Cs] [J | Js] Map [slot J Kind Args | Out] :-
    std.map Ds (translate-input Map) Args,
    expand-parts Cs Js [pr K J | Map] Out.

  pred resolve-entries i:list field-entry, i:list component, i:list (pair id term),
      o:list component, o:list prop.
  resolve-entries [] Cs _ Cs [].
  resolve-entries [entry Keys _ Head Selection Preferred | Entries] Available Env Out Heads :-
    coq.env.global Ref Head, coq.gref->id Ref M,
    if (mixin-spec Ref _ Params) true (coq.error "Unregistered Minks mixin:" M),
    if (mixin-combination Ref _ RawFixed RawParts Ctor _)
      (Ref = indt Interface, std.length RawFixed F,
       current-layout Interface F {std.append RawFixed RawParts} Ordinary Layout,
       std.split-at F Layout Fixed Parts, std.map Ordinary parameter-key Prefix,
       (source-keys Preferred => resolve-fixed M Head Selection Prefix Fixed Available Env Deps),
       std.map Fixed component-key FixedKeys,
       fixed-mapping {std.append Prefix FixedKeys} Deps Mapping,
       expand-parts Parts Keys Mapping New,
       if (Head = pglobal _ U) (Make = pglobal (indc Ctor) U) (Make = global (indc Ctor)),
       coq.typecheck Make Ty ok,
       std.map Deps (k\t\ lookup k Env t) Values,
       coq.subst-prod Values Ty FieldsTy, layout-heads FieldsTy New Here,
       Check = (bs\ sigma fields term\
         std.map Keys (k\t\ lookup k bs t) fields,
         coq.mk-app Make {std.append Values fields} term,
         std.assert-ok! (coq.typecheck term _) "Ill-typed exported field batch"))
      (Keys = [Key], resolve-arguments M Head Selection Params Available Env Deps,
       New = [slot Key (mixin-kind Ref) {key-inputs Deps}],
       Here = [selected-head Key (mixin-kind Ref) Head], Check = (_\ true)),
    with-heads Here (with-components New Env (bindings\
      Check bindings, resolve-entries Entries {std.append Available New} bindings Out Later)),
    std.append Here Later Heads.

  pred save-view i:struct-conversion.
  save-view (conversion Source Target Ref Mode) :-
    coq.elpi.accumulate execution-site "minks.flat.db"
      (clause _ _ (recorded-view Source Target Ref Mode)).

  pred scoped-args i:list argument, i:term, o:list argument.
  scoped-args [] (sort prop) [].
  scoped-args [str "#term" | Ts] Body [trm T | Out] :- !,
    Body = let _ _ T Rest,
    scoped-args Ts (Rest T) Out.
  scoped-args [A | Ts] T [A | Out] :- scoped-args Ts T Out.

  pred open-header i:arity, i:list header-binder, i:id, i:list argument.
  open-header (parameter N Kind Ty Rest) Rev ID Args :- !,
    coq.id->name N Name,
    @pi-decl Name Ty x\ open-header (Rest x) [binder N Kind Ty x | Rev] ID Args.
  open-header (arity Body) Rev ID Args :-
    std.rev Rev H, scoped-args Args Body Full,
    struct-universes (upoly-decl Named _ _ _),
    (header-universes Named :- !) => (local-header H :- !) => main [str ID | Full].

  main [str "#discharged", str Name] :- !,
    coq.locate Name (indt I), coq.env.current-path Here,
    flat-layout Here I Cs Fields,
    find-views I Cs Fields [] Views, std.forall Views save-view.
  main [upoly-const-decl ID none Arity UD | Args] :- !,
    struct-universes UD => open-header Arity [] ID Args.
  main [A | Args] :-
    if (atom A Name, struct-parents Args Applications Actuals Rest,
        parse-components Rest Slots Tail, parse-exports Tail Exports) true usage,
    resolve-bases Applications (parents\
      std.assert! (std.map2 parents Actuals parent-type Named) "could not align parent types",
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
         std.map Cs (c\n\ n = named-field {component-key c} [] []) Names,
         std.map Cs component-key Keys, minks.stored-projections I Fields,
         minks.register-keys I Keys Fields [],
         Registration = native-base Head I,
         Signature = declared (indt I) (packed [] Cs Names [] []),
         coq.elpi.accumulate execution-site "minks.flat.db" (clause _ _ Registration),
         coq.elpi.accumulate execution-site "minks.flat.db" (clause _ _ Signature),
         Registration => Signature => Continue I)
       (coq.error "Several visible bases for native parent; name the intended structure:" Head)).

  pred export-keys i:list (list component), i:list component, i:option (list id), o:list id.
  export-keys _ _ (some Keys) Keys.
  export-keys Parents Inherited none Keys :-
    std.map Inherited component-key Candidates,
    std.filter Candidates (k\ std.forall Parents (contains-key k)) Keys.

  % Parameters of an inherited structure specialize existing fields. Only
  % locally written entries introduce or reuse a contextual key declaration.
  pred key-row i:list (pair id gref), i:field-name-info, i:gref,
      o:id, o:gref, o:list id.
  key-row _ (named-field K _ [pr Parent Original | _]) _ K Source [] :- !,
    origin-projection Parent Original Source.
  key-row Defaults (named-field K History []) Projection Original Source [Original] :-
    if (std.rev History [First | _]) (Original = First) (Original = K),
    if (std.mem Defaults (pr Original Prior)) (Source = Prior) (Source = Projection).

  pred written-origins i:list id, o:list (pair id gref).
  written-origins Ks Origins :-
    std.map-filter Ks (k\pair\ sigma n p\ binding-key k n (some p), pair = pr n p) Origins.

  pred default-origins i:pending-slot, o:list (pair id gref).
  default-origins (pending (batch none _) Head _) Origins :- !,
    coq.env.global Ref Head, mixin-combination Ref _ _ Parts _ Ps,
    std.map2 Parts Ps (c\p\pair\ pair = pr {component-key c} (const p)) Origins.
  default-origins (pending (single K _) _ _) Origins :- !,
    written-origins [K] Origins.
  default-origins (pending (batch (some Ks) _) _ _) Origins :- !,
    written-origins Ks Origins.
  default-origins _ [].

  pred register-keys i:inductive, i:list pending-slot, i:list field-name-info.
  register-keys I Slots Names :-
    std.map Slots default-origins Groups, std.flatten Groups Defaults,
    minks.stored-projections I Ps,
    std.map2 Names Ps (n\p\row\ sigma k src declared\ key-row Defaults n p k src declared,
      row = pr (pr k src) declared) Rows,
    std.unzip Rows Pairs Locals, std.unzip Pairs Keys Sources,
    minks.register-keys I Keys Sources {std.flatten Locals},
    std.forall2 Ps Rows (p\r\ if (r = pr (pr K p) [K])
      (coq.elpi.accumulate execution-site "minks.flat.db" (clause _ _ (visible-key K p)))
      true).

  % Index each written rename at its declaration, including intermediate
  % spellings when the same field is renamed twice in this structure.
  pred register-aliases i:inductive, i:list pending-slot, i:list field-name-info.
  register-aliases I Slots Names :-
    std.map-filter Slots (s\a\ s = rename _ a) Aliases,
    if (Aliases = []) true (
      std.map Names (n\k\ n = named-field k _ _) Keys, stored-fields I Keys Fields,
      std.forall Aliases (a\ sigma k p\ final-name Names a k, std.mem Fields (pr k p),
        coq.elpi.accumulate execution-site "minks.flat.db" (clause _ _ (field-alias a p)))).

  pred build i:id, i:list struct-parent, i:list pending-slot, i:list (pair id (option (list id))).
  build Name Applications Slots Exports :-
    struct-ancestors Applications FlatParents,
    std.map Applications parent-names ParentNames,
    merge-names {std.flatten ParentNames} Initial,
    plan-entries Slots Initial Final Entries,
    std.forall Exports (e\ sigma ks\
      if (e = pr _ (some ks)) (std.forall ks (k\
        if (std.mem Final (named-field k _ _)) true (require-fresh Final k))) true),
    std.map Entries (e\ps\ e = entry _ ps _ _ _) Aliases,
    ancestors FlatParents [] All,
    scope-parent-keys All Final (
      std.map Applications parent-layout Branches, close-parents Branches Inherited,
      with-components Inherited [] (env\
        resolve-entries Entries Inherited env Components Heads),
      with-heads Heads (
          add-distinct FlatParents [] ParentsRev,
          declare-packed Name {std.rev ParentsRev} Components {std.flatten Aliases} I Args,
          align-field-names I Components Final Ordered,
          std.assert! (register-keys I Slots Ordered) "Missing component identity metadata",
          register-aliases I Slots Ordered,
          active-family I Args =>
            finish Name Applications Branches Inherited Exports FlatParents Components Ordered I)).

  pred finish i:id, i:list struct-parent, i:list (list component), i:list component,
      i:list (pair id (option (list id))), i:list inductive, i:list component, i:list field-name-info, i:inductive.
  finish Name Applications Branches Inherited Exports FlatParents Components Names I :-
    std.assert! (generate-views Name FlatParents Components I Views Packers)
      "Could not generate the structure",
    std.forall Views save-view,
    % Check exports in the context of the completed record and its actual inputs.
    active-family I Args,
    (struct-spec I Applications Components => parent-inputs I Args =>
      std.map Exports
        (e\out\ sigma label selection keys interface fixed\
          e = pr label selection, export-keys Branches Inherited selection keys,
          std.assert! (@keep-alg-univs! =>
            generate-relative Name I Components FlatParents Views label keys interface fixed)
            ("Could not generate relative interface " ^ label),
          out = pr interface fixed) Interfaces),
    Data = packed Applications Components Names Packers Interfaces,
    coq.elpi.accumulate execution-site "minks.flat.db" (clause _ _ (declared (indt I) Data)).
  main _ :- usage.
}}.
Elpi Accumulate Db minks.flat.db.

Elpi Command minks.inspect.
Elpi Accumulate Db Header minks.flat.db.
Elpi Accumulate Plugin "minks.combinations".
Elpi Accumulate File minks.spec.
Elpi Accumulate lp:{{
  pred inspect i:id, i:gref.
  inspect Name Ref :-
    mixin-spec Ref Direct Params, !,
    print-mixin Name Ref Direct Params.
  inspect Name Ref :-
    Ref = indt I, spec I Parents _, !,
    close I Cs, checked-field-names I Cs Names,
    struct-views I Views,
    metadata I (packed Declared _ _ Packers Exports),
    current-layout I 0 Cs Params Layout,
    inspection-names Names => print-struct Declared Name Params Parents Layout Views Packers Exports.

  main [str Name] :- !,
    coq.locate-all Name Found,
    if (std.mem Found (loc-gref Ref), inspect Name Ref) (Declaration = tt) (Declaration = ff),
    std.findall (field-alias Name _) Matches,
    std.map Matches (m\r\ sigma p\ m = field-alias _ p, r = const p) Aliases,
    std.map-filter Found (l\r\ l = loc-gref r) Refs,
    lookup-key Name _ _ Keys,
    if (minks.inspect-key Name Keys Aliases Refs) true
      (std.assert! (Declaration = tt) ("No registered Minks declaration or key named " ^ Name)).
  main _ :- coq.error "Usage: Minks.Inspect Name.".
}}.
Elpi Accumulate Db minks.flat.db.
