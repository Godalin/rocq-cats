From elpi Require Import elpi.

(** * Structure specifications

    Store inheritance by Rocq identity. Each component key names one
    selected mixin and its dependencies within a structure. *)

Declare ML Module "rocq-minks.plugin".

Elpi Db minks.flat.db lp:{{
  kind component type.
  kind native-head type.
  type sort-head native-head.
  type ref-head gref -> native-head.
  kind field-kind type.
  type mixin-kind gref -> field-kind.
  type native-kind native-head -> field-kind.
  kind input type.
  type key-input id -> input.
  kind scoped-term type.
  type scope-arg (term -> scoped-term) -> scoped-term.
  type scope-body term -> scoped-term.
  type host-input scoped-term -> list input -> input.
  type projection-input constant -> list input -> input.
  type slot id -> field-kind -> list input -> component.

  kind mixin-param type.
  type mixin-val mixin-param.
  kind argument-ref type.
  type position int -> argument-ref.
  type section-ref constant -> argument-ref.
  type host-ref scoped-term -> list argument-ref -> argument-ref.
  type projection-ref constant -> list argument-ref -> argument-ref.
  type mixin-scoped-dep gref -> list argument-ref -> mixin-param.
  type mixin-dep gref -> list int -> mixin-param.

  pred mixin-spec i:gref, o:list gref, o:list mixin-param.
  kind minks-export type.
  type relative-interface option inductive -> list component -> list component ->
      constructor -> list constant -> minks-export.
  kind struct-parent type.
  type native-parent native-head -> list id -> struct-parent.
  type named-parent inductive -> list id -> struct-parent.

  pred native-base i:native-head, o:inductive.
  kind view-registration type.
  type explicit-view, coercion-view, canonical-view,
    coercion-canonical-view view-registration.

  kind struct-conversion type.
  type conversion inductive -> inductive -> constant -> view-registration
    -> struct-conversion.

  kind field-name-info type.
  type named-field id -> list id -> list (pair inductive id) -> field-name-info.
  kind declaration type.
  type relative minks-export -> declaration.
  type packed list struct-parent -> list component -> list field-name-info ->
      list constant -> list (pair inductive (list id)) -> declaration.
  typeabbrev role (option (option (pair id gref))).
  type primitive list gref -> list role -> declaration.
  pred declared i:gref, o:declaration.
  pred recorded-view i:inductive, o:inductive, o:constant, o:view-registration.
  pred visible-key i:id, o:gref.
  external pred minks.owned-key i:(pair modpath id), o:gref.
  typeabbrev module-info (pair declaration (list struct-conversion)).
  external pred minks.local-info i:gref, o:module-info.
  pred field-alias i:id, o:constant.
  pred flat-layout i:list string, o:inductive, o:list component,
      o:list (pair id constant).
}}.

Elpi File minks.spec lp:{{
  pred projection-app i:term, o:constant, o:list term.
  projection-app T C Args :-
    coq.safe-dest-app T Head Args, Args = [_ | _],
    coq.env.global (const C) Head, coq.env.projection? C _.

  pred atom i:argument, o:id.
  atom (str Name) Name :-
    not (std.mem ["extends", "with", "as", "exports", ",", ":", "[", "]"] Name).

  pred ids i:list argument, o:list id, o:list argument.
  ids [A | Rest] [Name | Names] Tail :-
    atom A Name,
    ids-rest Rest Names Tail.

  pred ids-rest i:list argument, o:list id, o:list argument.
  ids-rest [str "," | Rest] Names Tail :- !, ids Rest Names Tail.
  ids-rest Rest [] Rest.

  pred parameter-index i:list term, i:term, o:int.
  parameter-index [X | _] X 0 :- !.
  parameter-index [_ | Vars] X N :-
    parameter-index Vars X M,
    N is M + 1.

  % A binder inside an open section is referenced directly until discharge.
  pred parameter-ref i:list term, i:term, o:argument-ref.
  parameter-ref Vars A (position I) :- parameter-index Vars A I, !.
  parameter-ref _ (global (const C)) (section-ref C) :-
    coq.env.section-variables Cs, std.mem Cs C.

  pred parameter-term i:list term, i:argument-ref, o:term.
  parameter-term Vars (position I) T :- std.nth I Vars T.
  parameter-term _ (section-ref C) (global (const C)).

  pred argument-ref-of i:list term, i:term, o:argument-ref.
  argument-ref-of Vars A Ref :- parameter-ref Vars A Ref, !.
  argument-ref-of Vars T (projection-ref C Refs) :-
    projection-app T C Args, !, std.map Args (argument-ref-of Vars) Refs.
  argument-ref-of Vars T (host-ref Expr Refs) :-
    std.map Vars (x\p\ sigma i\ parameter-index Vars x i, p = pr x (position i)) Local,
    coq.env.section-variables Cs,
    std.map Cs (c\p\ p = pr (global (const c)) (section-ref c)) Ambient,
    scope-term {std.append {std.rev Local} Ambient} T Expr Refs.

  % Only regular Elpi clauses hold declaration data. A qualified lookup
  % reads the same rows in the defining module's scope.
  pred recorded-views i:inductive, o:list struct-conversion.
  recorded-views I Views :-
    std.findall (recorded-view I _ _ _) Rows,
    std.map Rows (r\v\ sigma t c m\ r = recorded-view I t c m,
      v = conversion I t c m) Views.

  minks.local-info (indt I) (pr Data Views) :-
    declared (indt I) Data, recorded-views I Views.

  minks.owned-key (pr MP Key) P :-
    visible-key Key P, coq.gref->path P {coq.modpath->path MP}.

  % A path still under construction can already contribute visible rows.
  % Resolve closed paths using Rocq's module names, including module aliases.
  pred qualified-key i:list string, i:id, o:gref.
  qualified-key Prefix K P :-
    std.string.concat "." Prefix Name, coq.locate-all Name Matches,
    if (std.mem Matches (loc-modpath MP))
      (if (minks.owned-key (pr MP K) P) true (minks.scoped-key MP K P))
      (visible-key K P, coq.gref->path P Path, std.appendR _ Prefix Path,
       coq.env.current-path Here, std.appendR Path _ Here).

  pred lookup-key i:id, o:id, o:list string, o:list gref.
  lookup-key Name Short Prefix Keys :-
    rex.split "[.]" Name Parts, std.rev Parts [Short | Rev], std.rev Rev Prefix,
    if (Prefix = [])
      (coq.env.current-path Here,
       if (visible-key Short P, coq.gref->path P Here) (Keys = [P])
         (std.findall (visible-key Short _) Rows,
          std.map Rows (r\p\ r = visible-key Short p) Keys))
      (if (qualified-key Prefix Short P) (Keys = [P]) (Keys = [])).

  pred binding-key i:id, o:id, o:option gref.
  binding-key Name Short Source :-
    lookup-key Name Short Prefix Keys,
    if (Keys = [P]) (Source = some P)
      (if (Keys = [])
         (if (Prefix = []) (Source = none) (coq.error "Unknown Minks key:" Name))
         (coq.error "Ambiguous Minks key; qualify its module:" Short Keys)).

  pred metadata i:inductive, o:declaration.
  metadata I Data :- declared (indt I) Local, !, Data = Local.
  metadata I Data :- minks.scoped-info I (pr Data _).

  pred struct-spec i:inductive, o:list struct-parent, o:list component.
  struct-spec I Parents Cs :- metadata I (packed Parents Cs _ _ _).

  pred struct-views i:inductive, o:list struct-conversion.
  struct-views I Vs :- declared (indt I) _, !, recorded-views I Vs.
  struct-views I Vs :- minks.scoped-info I (pr (packed _ _ _ _ _) Vs).

  pred struct-view i:inductive, i:inductive, o:constant, o:view-registration.
  struct-view I T C M :- struct-views I Views, std.mem Views (conversion I T C M).

  pred mixin-roles i:inductive, o:list gref, o:list role.
  mixin-roles I Parents Roles :-
    metadata I (primitive Parents Stored),
    coq.env.indt I tt N _ _ _ _,
    Extra is N - {std.length Stored},
    std.assert! (Extra >= 0) "A registered mixin has fewer parameters than its declared roles",
    std.map {std.iota Extra} (_\r\ r = none) Prefix, std.append Prefix Stored Roles.

  pred mixin-combination i:gref, o:option inductive, o:list component, o:list component,
      o:constructor, o:list constant.
  mixin-combination (indt I) Base Fixed Remaining Ctor Origins :-
    metadata I (relative Layout),
    Layout = relative-interface Base Fixed Remaining Ctor Origins.

  pred mixin-header i:inductive, o:list gref, o:list int.
  mixin-header I [] Values :-
    mixin-combination (indt I) _ _ _ _ _, !,
    coq.env.indt I tt N _ _ _ _, std.iota N Values.
  mixin-header I Parents Values :-
    mixin-roles I Parents Roles,
    std.length Roles N, std.zip {std.iota N} Roles Indexed,
    std.map-filter Indexed (p\i\ p = pr i none) Values.

  pred read-dependencies i:term, i:list term, i:int, i:list int, o:list mixin-param.
  read-dependencies (prod _ _ Body) Vars Pos [Pos | Values] [mixin-val | Params] :- !,
    Next is Pos + 1,
    pi x\ read-dependencies (Body x) {std.append Vars [x]} Next Values Params.
  read-dependencies (let _ _ Value Body) Vars Pos Values Params :- !,
    read-dependencies (Body Value) Vars Pos Values Params.
  read-dependencies (sort _) _ _ [] [].
  read-dependencies (prod _ Ty Body) Vars Pos Values
      [Dep | Params] :-
    coq.safe-dest-app Ty Head Args,
    coq.env.global Ref Head,
    Ref = indt I, mixin-header I _ _,
    std.map Args (argument-ref-of Vars) Refs,
    if (std.map Refs (r\i\ r = position i) Positions)
      (Dep = mixin-dep Ref Positions) (Dep = mixin-scoped-dep Ref Refs),
    Next is Pos + 1,
    pi x\ read-dependencies (Body x) {std.append Vars [x]} Next Values Params.

  pred read-mixin i:gref, i:list int, o:list mixin-param.
  read-mixin Ref Values Params :-
    coq.env.typeof Ref Ty,
    read-dependencies Ty [] 0 Values Params.

  mixin-spec (indt I) Parents Params :-
    mixin-header I Parents Values,
    read-mixin (indt I) Values Params.

  pred mixin-head i:mixin-param, o:gref.
  mixin-head (mixin-dep Ref _) Ref.
  mixin-head (mixin-scoped-dep Ref _) Ref.

  % Ordinary parameter references and field keys occupy disjoint namespaces.
  pred parameter-key i:id, o:id.
  parameter-key Name Key :- Key is "param:" ^ Name.
  kind header-binder type.
  type binder id -> implicit_kind -> term -> term -> header-binder.
  pred local-header o:list header-binder.
  local-header [].

  pred ordinary-binding o:id, o:term.
  ordinary-binding Name Var :-
    local-header H, std.mem H (binder Name _ _ Var).
  ordinary-binding Name (global (const C)) :-
    coq.env.section-variables Vars, std.mem Vars C, coq.gref->id (const C) Name.

  pred ordinary-input i:id, o:id, o:term.
  ordinary-input Name Key Var :- ordinary-binding Name Var, parameter-key Name Key.

  pred ambient-value i:id, o:term.
  ambient-value Key Var :- ordinary-binding Name Var, parameter-key Name Key.

  pred key-inputs i:list id, o:list input.
  key-inputs Keys Inputs :- std.map Keys (k\r\ r = key-input k) Inputs.

  pred argument-input i:list id, i:argument-ref, o:input.
  argument-input Keys (position I) (key-input K) :- std.nth I Keys K.
  argument-input _ (section-ref C) (key-input K) :-
    coq.gref->id (const C) Name, ordinary-input Name K _.
  argument-input Keys (projection-ref C Args) (projection-input C Inputs) :-
    std.map Args (argument-input Keys) Inputs.
  argument-input Keys (host-ref Expr Refs) (host-input Expr Inputs) :-
    std.map Refs (argument-input Keys) Inputs.

  pred input-term i:list (pair id term), i:input, o:term.
  pred component-env o:list (pair id term).
  component-env [].
  pred same-input i:list (pair id term), i:input, i:input.
  same-input _ X X :- !.
  same-input Fields X Y :-
    input-keys X Xs, input-keys Y Ys,
    std.forall Xs (std.mem Ys), std.forall Ys (std.mem Xs),
    std.forall Xs (k\ (ambient-value k _ ; std.mem Fields (pr k _))),
    input-term Fields X T, input-term Fields Y U,
    coq.elaborate-skeleton T _ L ok, coq.elaborate-skeleton U _ R ok,
    coq.unify-eq L R ok.

  pred selected-witness i:list component, i:list (pair id term), i:gref, i:list input, o:id.
  selected-witness Cs Fields Ref Deps Key :-
    std.mem Cs (slot Key (mixin-kind Ref) Actual),
    std.forall2 Deps Actual (same-input Fields).
  selected-witness _ Fields _ _ Key :-
    std.mem Fields (pr Key _), ambient-value Key _.

  pred mixin-arguments i:list mixin-param, i:list component, i:list (pair id term),
      i:list id, o:list id.
  mixin-arguments [] _ _ Keys Keys.
  mixin-arguments [mixin-val | Params] Cs Fields Keys Args :-
    std.mem Fields (pr Key _),
    mixin-arguments Params Cs Fields {std.append Keys [Key]} Args.
  mixin-arguments [mixin-dep Ref Positions | Params] Cs Fields Keys Args :-
    std.map Positions (i\k\ std.nth i Keys k) Names, key-inputs Names Deps,
    selected-witness Cs Fields Ref Deps Key,
    mixin-arguments Params Cs Fields {std.append Keys [Key]} Args.

  mixin-arguments [mixin-scoped-dep Ref Refs | Params] Cs Fields Keys Args :-
    std.map Refs (argument-input Keys) Deps,
    selected-witness Cs Fields Ref Deps Key,
    mixin-arguments Params Cs Fields {std.append Keys [Key]} Args.

  pred field-type i:component, i:list (pair id term), o:term.

  pred compatible-field i:list (pair id term), i:field-kind, i:list input,
      i:field-kind, i:list input.
  compatible-field Env (mixin-kind Ref) Args (mixin-kind Ref) Other :-
    std.forall2 Args Other (same-input Env).
  compatible-field Env (native-kind A) Args (native-kind B) Other :-
    if (A = B, std.forall2 Args Other (same-input Env)) true (
      field-type (slot "" (native-kind A) Args) Env Left,
      field-type (slot "" (native-kind B) Other) Env Right,
      coq.unify-eq Left Right ok).

  pred available-component i:list component, o:id, i:field-kind, i:list input.
  available-component Cs Key Kind Deps :-
    std.mem Cs (slot Key Other Actual), component-env Env,
    compatible-field Env Kind Deps Other Actual.

  pred source-keys o:list (pair id id).
  pred match-component i:id, i:field-kind, i:list input, i:list component,
      i:list id, o:id.
  match-component Key Kind Deps Available Used Actual :-
    if (source-keys Names, std.mem Names (pr Key Original),
        available-component Available Original Kind Deps, not (std.mem Used Original))
      (Actual = Original)
      (available-component Available Actual Kind Deps, not (std.mem Used Actual)).

  pred translate-key i:list (pair id id), i:id, o:id.
  translate-key Mapping Key Actual :- std.mem Mapping (pr Key Actual), !.
  translate-key _ Key Key :- ambient-value Key _.

  pred translate-input i:list (pair id id), i:input, o:input.
  translate-input Mapping (key-input K) (key-input Actual) :- translate-key Mapping K Actual.
  translate-input Mapping (projection-input C Args) (projection-input C Inputs) :-
    std.map Args (translate-input Mapping) Inputs.

  translate-input Mapping (host-input Expr Args) (host-input Expr Inputs) :-
    std.map Args (translate-input Mapping) Inputs.

  pred input-keys i:input, o:list id.
  input-keys (key-input K) [K].
  input-keys (projection-input _ Args) Keys :- std.map Args input-keys Lists, std.flatten Lists Keys.

  input-keys (host-input _ Args) Keys :- std.map Args input-keys Lists, std.flatten Lists Keys.

  pred input-text i:input, o:id.
  input-text (key-input K) K.
  input-text (projection-input C Args) Text :-
    coq.gref->id (const C) Name, std.map Args input-text Labels,
    Text is "(" ^ Name ^ " " ^ {std.string.concat " " Labels} ^ ")".

  input-text (host-input Expr Args) Text :-
    std.map Args input-text Labels, print-scoped Expr Labels Body,
    Text is "(" ^ Body ^ ")".

  pred print-scoped i:scoped-term, i:list id, o:id.
  print-scoped (scope-body T) [] Text :- @ppall! => coq.term->string T Text.
  print-scoped (scope-arg Body) [Key | Keys] Text :-
    rex.replace "^param:" "" Key Label, coq.id->name Label Name,
    @pi-decl Name (sort prop) x\ print-scoped (Body x) Keys Text.

  pred mapped-components i:list component, i:list component,
      i:list (pair id id), i:list id, o:list id.
  mapped-components [] _ _ _ [].
  mapped-components [C | Cs] Available Mapping Used
      [Actual | Args] :-
    C = slot Key Kind Deps,
    std.map Deps (translate-input Mapping) ActualDeps,
    match-component Key Kind ActualDeps Available Used Actual,
    mapped-components Cs Available [pr Key Actual | Mapping] [Actual | Used] Args.

  pred print-mixin i:id, i:gref, i:list gref, i:list mixin-param.
  print-mixin Name Ref Direct Params :-
    std.map Direct coq.gref->id Parents,
    Title is "Minks mixin " ^ Name,
    Dependencies is "Direct dependencies: [" ^ {std.string.concat ", " Parents} ^ "]",
    Order is "Parameter order: " ^ {term_to_string Params},
    combination-lines Ref Extra,
    coq.say {std.string.concat "\n" [Title, Dependencies, Order | Extra]}.

  % Re-read the discharged constructor: Rocq can generalize different
  % section inputs for a component class and its enclosing record.
  pred input-label i:list (pair term id), i:term, o:id.
  input-label Inputs Arg Label :- std.mem Inputs (pr Arg Label), !.
  input-label _ Var Key :- ordinary-binding Name Var, parameter-key Name Key.

  % Abstract exactly the selected inputs that occur in the host term. Rocq
  % supplies the entire body, including coercions and their implicit inputs.
  pred scope-term i:list (pair term A), i:term, o:scoped-term, o:list A.
  scope-term [] T (scope-body Body) [] :- copy T Body.
  scope-term [pr Var Key | Rest] T Expr Args :-
    if (pi marker\ sigma body\ ((copy Var marker :- !) => copy T body), occurs marker body)
      (Expr = scope-arg Body, Args = [Key | More],
       pi x\ (copy Var x :- !) => scope-term Rest T (Body x) More)
      (scope-term Rest T Expr Args).

  pred open-scoped i:scoped-term, i:list term, o:term.
  open-scoped (scope-body T) [] T.
  open-scoped (scope-arg Body) [Arg | Args] T :- open-scoped (Body Arg) Args T.

  pred layout-input i:list (pair term id), i:term, o:input.
  layout-input Inputs T (key-input Key) :- input-label Inputs T Key, !.
  layout-input Inputs T (projection-input C Args) :-
    projection-app T C Terms, !, std.map Terms (layout-input Inputs) Args.
  layout-input Inputs T (host-input Expr Args) :-
    std.findall (ordinary-binding _ _) Bindings,
    std.map Bindings (b\p\ sigma n x\ b = ordinary-binding n x, p = pr x {parameter-key n}) Ambient,
    scope-term {std.append Inputs Ambient} T Expr Keys, key-inputs Keys Args.

  pred read-layout i:term, i:int, i:list (pair term id), i:list component,
      o:list id, o:list component.
  read-layout (prod Name _ Body) N Inputs Cs [Label | Params] Out :-
    N > 0, !, coq.name->id Name Label, Next is N - 1,
    parameter-key Label Key,
    pi x\ read-layout (Body x) Next [pr x Key | Inputs] Cs Params Out.
  read-layout Ty 0 Inputs Cs [] Out :- read-slots Ty Inputs Cs Out.

  pred read-slots i:term, i:list (pair term id), i:list component, o:list component.
  read-slots _ _ [] [].
  read-slots (prod _ Ty Body) Inputs [slot Key Kind _ | Cs] [slot Key Kind Args | Rest] :-
    coq.safe-dest-app Ty _ Terms, std.map Terms (layout-input Inputs) Args,
    pi x\ read-slots (Body x) [pr x Key | Inputs] Cs Rest.

  pred current-layout i:inductive, i:int, i:list component, o:list id, o:list component.
  current-layout I Fixed Cs Params Layout :-
    coq.env.indt I tt N _ _ [K] _,
    Extra is N - Fixed,
    coq.env.typeof (indc K) Ty,
    read-layout Ty Extra [] Cs Params Layout.

  pred export-field-lines i:inductive, i:list component, o:list string.
  export-field-lines I Cs Lines :-
    coq.env.projections I Ps,
    std.map2 Cs Ps (c\p\line\ sigma ref proj db mode\
      if (c = slot _ (mixin-kind ref) _, p = some proj,
          coq.TC.db-for ref db, std.mem db (tc-instance (const proj) _))
        (mode = " [instance]")
        (if (c = slot _ (native-kind _) _) (mode = " [Coercion]") (mode = " [explicit]")),
      slot-line [] mode c line) Lines.

  pred section-lines i:string, i:list string, o:list string.
  section-lines _ [] [].
  section-lines Title [Line | Lines] [Title, Line | Lines].

  pred combination-lines i:gref, o:list string.
  combination-lines Ref Lines :-
    mixin-combination Ref (some Base) Fixed Remaining _ _, !,
    coq.gref->id (indt Base) BaseName,
    BaseLine is "Packed base: " ^ BaseName,
    std.map Fixed (slot-line [] " [fixed]") FixedLines,
    section-lines "Additional fixed components:" FixedLines Additional,
    Ref = indt Export, export-field-lines Export Remaining Fields,
    std.append [BaseLine | Additional] ["Remaining components:" | Fields] Lines.
  combination-lines Ref Lines :-
    mixin-combination Ref _ Fixed Parts _ _, !,
    std.map Fixed component-key Keys,
    FixedLine is "Fixed keys: [" ^ {std.string.concat ", " Keys} ^ "]",
    Ref = indt I, std.length Fixed F,
    current-layout I F {std.append Fixed Parts} _ Layout,
    std.drop F Layout Remaining, export-field-lines I Remaining Fields,
    Lines = [FixedLine, "Expanded components:" | Fields].
  combination-lines _ [].

  % Account for each metadata row exactly once, in physical field order.
  pred align-field-names i:inductive, i:list component, i:list field-name-info,
      o:list field-name-info.
  align-field-names _ [] [] [] :- !.
  align-field-names I [] Extra _ :- coq.error "Unexpected field metadata in" I Extra.
  align-field-names I [slot Key _ _ | Cs] Rows [Row | Ordered] :-
    std.partition Rows (r\ r = named-field Key _ _) Matches Rest,
    if (Matches = [Row]) true
      (coq.error "Expected exactly one field metadata entry in" I "for key" Key),
    align-field-names I Cs Rest Ordered.

  pred checked-field-names i:inductive, i:list component, o:list field-name-info.
  checked-field-names I Cs Names :-
    metadata I (packed _ _ Rows _ _),
    align-field-names I Cs Rows Names.

  pred struct-ancestors i:list struct-parent, o:list inductive.
  struct-ancestors Ps Is :-
    std.map-filter Ps (p\i\ p = named-parent i _, struct-spec i _ _) Is.

  pred spec i:inductive, o:list inductive, o:list component.
  spec I Parents Cs :- struct-spec I Ps Cs, struct-ancestors Ps Parents.

  pred ancestors i:list inductive, i:list inductive, o:list inductive.
  ancestors [] Seen Seen.
  ancestors [P | Parents] Seen All :-
    if (std.mem Seen P) (ancestors Parents Seen All) (
      spec P More _,
      ancestors More [P | Seen] Next,
      ancestors Parents Next All).

  pred contains-key i:id, i:list component.
  contains-key Key Cs :- std.mem Cs (slot Key _ _).

  pred merge i:list component, i:list component, o:list component.
  merge [] Cs Cs.
  merge [C | Rest] Cs Out :-
    component-key C Key,
    if (contains-key Key Cs)
      (if (C = slot Key Kind Inputs, available-component Cs Key Kind Inputs) (Next = Cs)
         (coq.error "Incompatible definitions of component" Key))
      (std.append Cs [C] Next),
    merge Rest Next Out.

  pred close i:inductive, o:list component.
  close I Cs :- parent-components I Cs, !.
  close I Cs :- struct-spec I _ Cs.

  % During one declaration these entries specialize previously discharged parents.
  pred parent-inputs i:inductive, o:list term.
  pred parent-components i:inductive, o:list component.

  pred shared-key i:id, i:list (list component).
  shared-key Key [Branch | Branches] :-
    if (contains-key Key Branch)
      (std.exists Branches (contains-key Key))
      (shared-key Key Branches).

  pred parent-layout i:struct-parent, o:list component.
  parent-layout (named-parent I _) Cs :- close I Cs.
  pred close-parents i:list (list component), o:list component.
  close-parents Branches Cs :-
    std.fold Branches [] merge Ordered,
    std.partition Ordered (c\ shared-key {component-key c} Branches) Shared Rest,
    std.append Shared Rest Cs.

  % Keep the first key for each class head in the complete packed order.
  pred auto-instance i:list component, i:component.
  auto-instance Cs (slot Key (mixin-kind Ref) _) :-
    coq.TC.class? Ref,
    std.filter Cs (c\ c = slot _ (mixin-kind Ref) _) [slot Key _ _ | _].

  pred component-key i:component, o:id.
  component-key (slot K _ _) K.

  pred inspection-names o:list field-name-info.

  pred parent-sources i:list inductive, i:id, o:list id.
  parent-sources [] _ [].
  parent-sources [P | Ps] Key Sources :-
    parent-sources Ps Key Rest,
    if (inspection-names Names, std.mem Names (named-field Key _ Origins),
        std.mem Origins (pr P _))
      (coq.gref->id (indt P) Name, Sources = [Name | Rest])
      (Sources = Rest).

  pred slot-line i:list inductive, i:string, i:component, o:string.
  slot-line Parents Mode (slot Key (mixin-kind Ref) Deps) Line :-
    coq.gref->id Ref Mixin,
    parent-sources Parents Key Sources,
    std.map Deps input-text Labels,
    DepText is "[" ^ {std.string.concat ", " Labels} ^ "]",
    if (Sources = []) (Suffix = " (declared here)")
      (Suffix is " (from " ^ {std.string.concat ", " Sources} ^ ")"),
    Line is "  " ^ Key ^ " : " ^ Mixin ^ " " ^ DepText ^ Suffix ^ Mode.

  slot-line _ Mode (slot Key (native-kind Head) Args) Line :-
    std.map Args input-text Labels, parent-label (native-parent Head Labels) Label,
    Line is "  " ^ Key ^ " : " ^ Label ^ Mode.

  pred registration-label i:view-registration, o:string.
  registration-label explicit-view "explicit".
  registration-label coercion-view "Coercion".
  registration-label canonical-view "Canonical".
  registration-label coercion-canonical-view "Coercion, Canonical".

  pred view-line i:struct-conversion, o:string.
  view-line (conversion _ _ Ref Registration) Line :-
    coq.gref->id (const Ref) Name,
    registration-label Registration Label,
    Line is "  " ^ Name ^ " [" ^ Label ^ "]".

  pred packer-line i:constant, o:string.
  packer-line Ref Line :-
    coq.gref->id (const Ref) Name,
    Line is "  " ^ Name.

  pred export-line i:(pair inductive (list id)), o:string.
  export-line (pr Export Keys) Line :-
    coq.gref->id (indt Export) Name,
    Line is "  " ^ Name ^ " [" ^ {std.string.concat ", " Keys} ^ "]".

  pred parent-label i:struct-parent, o:id.
  parent-label (native-parent sort-head []) "Type".
  parent-label (native-parent (ref-head Ref) Args) Label :-
    coq.gref->id Ref Head, std.string.concat " " [Head | Args] Label.
  parent-label (named-parent I Args) Label :-
    coq.gref->id (indt I) Head, std.string.concat " " [Head | Args] Label.

  pred print-struct i:list struct-parent, i:id, i:list id, i:list inductive, i:list component,
      i:list struct-conversion, i:list constant, i:list (pair inductive (list id)).
  print-struct Declared Name Params Parents Cs Views Packers Exports :-
    std.map Declared parent-label Names,
    Title is "Minks structure " ^ Name,
    if (Params = []) (Header = [Title])
      (ParamLine is "Parameters: [" ^ {std.string.concat ", " Params} ^ "]",
       Header = [Title, ParamLine]),
    if (Names = []) (ParentLine = "Direct parents: none")
      (ParentLine is "Direct parents: " ^ {std.string.concat ", " Names}),
    std.map Cs (c\lines\ sigma mode line history\
      if (c = slot _ (native-kind _) _) (mode = " [Coercion]")
        (if (auto-instance Cs c) (mode = " [instance]") (mode = " [explicit]")),
      slot-line Parents mode c line,
      if (inspection-names Ns, std.mem Ns (named-field {component-key c} history _),
          history = [_ | _])
        (sigma retired\ retired is "    Retired keys: [" ^ {std.string.concat ", " history} ^ "]",
         lines = [line, retired]) (lines = [line])) FieldRows,
    section-lines "Conversions:" {std.map Views view-line} Conversions,
    section-lines "Packing functions:" {std.map Packers packer-line} Packing,
    section-lines "Relative interfaces:" {std.map Exports export-line} Interfaces,
    std.flatten [Header, [ParentLine, "Packed fields:"], {std.flatten FieldRows},
                 Conversions, Packing, Interfaces] Lines,
    coq.say {std.string.concat "\n" Lines}.
}}.
