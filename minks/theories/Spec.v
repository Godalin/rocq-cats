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
  pred mixin-combination o:gref, o:list component, o:list component, o:constructor.
  kind struct-parent type.
  type native-parent native-head -> list id -> struct-parent.
  type named-parent inductive -> list id -> struct-parent.

  pred native-base i:native-head, o:inductive.
  pred struct-spec i:inductive, o:list struct-parent, o:list component.
  kind view-registration type.
  type explicit-view, coercion-view, canonical-view,
    coercion-canonical-view view-registration.

  kind struct-conversion type.
  type conversion inductive -> inductive -> constant -> view-registration
    -> struct-conversion.

  pred struct-view i:inductive, o:inductive, o:constant, o:view-registration.
  pred struct-packer i:inductive, o:constant.
  pred struct-export i:inductive, o:inductive, o:list id.
  pred export-base i:gref, o:inductive.
  pred struct-assembly i:inductive, o:constant, o:list id.
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

  pred argument-ref-of i:list term, i:term, o:argument-ref.
  argument-ref-of Vars A (position I) :- parameter-index Vars A I, !.
  argument-ref-of _ (global (const C)) (section-ref C) :-
    coq.env.section-variables Cs, std.mem Cs C, !.

  argument-ref-of Vars T (projection-ref C Refs) :-
    projection-app T C Args, !, std.map Args (argument-ref-of Vars) Refs.
  argument-ref-of Vars T (host-ref Expr Refs) :-
    std.map Vars (x\p\ sigma i\ parameter-index Vars x i, p = pr x (position i)) Local,
    coq.env.section-variables Cs,
    std.map Cs (c\p\ p = pr (global (const c)) (section-ref c)) Ambient,
    scope-term {std.append {std.rev Local} Ambient} T Expr Refs.

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
    Ref = indt I, minks.mixin-header I _ _,
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
    minks.mixin-header I Parents Values,
    read-mixin (indt I) Values Params.

  pred mixin-head i:mixin-param, o:gref.
  mixin-head (mixin-dep Ref _) Ref.
  mixin-head (mixin-scoped-dep Ref _) Ref.

  % Ordinary parameter references and field keys occupy disjoint namespaces.
  pred parameter-key i:id, o:id.
  parameter-key Name Key :- Key is "param:" ^ Name.
  pred section-input i:id, o:id, o:term.
  section-input Name Key (global (const C)) :-
    coq.env.section-variables Vars, std.mem Vars C, coq.gref->id (const C) Name,
    parameter-key Name Key.

  pred ambient-value i:id, o:term.
  ambient-value Key T :-
    coq.env.section-variables Vars, std.mem Vars C, coq.gref->id (const C) Name,
    parameter-key Name Key, T = global (const C).

  pred explicit-input i:list (pair id term), i:id, o:id.
  explicit-input Fields Name Key :-
    if (section-input Name Ambient _)
      (if (std.mem Fields (pr Name _))
        (coq.error "Both a section parameter and a field have the name:" Name)
        (Key = Ambient))
      (if (std.mem Fields (pr Name _)) (Key = Name)
        (coq.error "Unknown component input:" Name)).

  pred key-inputs i:list id, o:list input.
  key-inputs Keys Inputs :- std.map Keys (k\r\ r = key-input k) Inputs.

  pred argument-input i:list id, i:argument-ref, o:input.
  argument-input Keys (position I) (key-input K) :- std.nth I Keys K.
  argument-input _ (section-ref C) (key-input K) :-
    coq.gref->id (const C) Name, section-input Name K _.
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

  pred available-component i:list component, o:id, i:field-kind, i:list input.
  available-component Cs Key Kind Deps :-
    std.mem Cs (slot Key Kind Actual), component-env Env,
    std.forall2 Deps Actual (same-input Env).

  pred match-component i:id, i:field-kind, i:list input, i:list component,
      i:list id, o:id.
  match-component Key Kind Deps Available Used Actual :-
    if (available-component Available Key Kind Deps, not (std.mem Used Key))
      (Actual = Key)
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

  pred print-mixin i:id, i:list gref, i:list mixin-param.
  print-mixin Name Direct Params :-
    Title is "Minks mixin " ^ Name,
    coq.say Title,
    std.map Direct coq.gref->id Parents,
    coq.say "Direct dependencies:" Parents,
    coq.say "Parameter order:" Params.

  % Re-read the discharged constructor: Rocq can generalize different
  % section inputs for a component class and its enclosing record.
  pred input-label i:list (pair term id), i:term, o:id.
  input-label Inputs Arg Label :- std.mem Inputs (pr Arg Label), !.
  input-label _ (global (const C)) Label :-
    coq.env.section-variables Vars, std.mem Vars C,
    coq.gref->id (const C) Name, parameter-key Name Label.

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
    coq.env.section-variables Vars,
    std.map Vars (c\p\ sigma name key\ coq.gref->id (const c) name, parameter-key name key,
      p = pr (global (const c)) key) Ambient,
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

  pred print-export-fields i:inductive, i:list component.
  print-export-fields I Cs :-
    coq.env.projections I Ps,
    std.forall2 Cs Ps (c\p\ sigma ref proj db mode\
      if (c = slot _ (mixin-kind ref) _, p = some proj,
          coq.TC.db-for ref db, std.mem db (tc-instance (const proj) _))
        (mode = " [instance]")
        (if (c = slot _ (native-kind _) _) (mode = " [Coercion]") (mode = " [explicit]")),
      print-slot [] mode c).

  pred print-combination i:gref.
  print-combination Ref :-
    export-base Ref Base, !, mixin-combination Ref Fixed Remaining _,
    coq.gref->id (indt Base) BaseName,
    coq.say "Packed base:" BaseName,
    Ref = indt Export,
    if (Fixed = []) true (
      coq.say "Additional fixed components:",
      std.forall Fixed (print-slot [] " [fixed]")),
    coq.say "Remaining components:",
    print-export-fields Export Remaining.

  print-combination Ref :-
    if (mixin-combination Ref Fixed Parts _)
      (std.map Fixed component-key FixedKeys,
       coq.say "Fixed keys:" FixedKeys,
       Ref = indt I, std.length Fixed F,
       current-layout I F {std.append Fixed Parts} _ Layout,
       std.drop F Layout Remaining,
       coq.say "Expanded components:",
       print-export-fields I Remaining)
      true.

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

  pred parent-sources i:list inductive, i:id, o:list id.
  parent-sources [] _ [].
  parent-sources [P | Ps] Key Sources :-
    close P Cs,
    parent-sources Ps Key Rest,
    if (contains-key Key Cs)
      (coq.gref->id (indt P) Name, Sources = [Name | Rest])
      (Sources = Rest).

  pred print-slot i:list inductive, i:string, i:component.
  print-slot Parents Mode (slot Key (mixin-kind Ref) Deps) :-
    coq.gref->id Ref Mixin,
    parent-sources Parents Key Sources,
    std.map Deps input-text Labels,
    DepText is "[" ^ {std.string.concat ", " Labels} ^ "]",
    if (Sources = []) (Suffix = " (declared here)")
      (Suffix is " (from " ^ {std.string.concat ", " Sources} ^ ")"),
    Line is "  " ^ Key ^ " : " ^ Mixin ^ " " ^ DepText ^ Suffix ^ Mode,
    coq.say Line.

  print-slot _ Mode (slot Key (native-kind Head) Args) :-
    std.map Args input-text Labels, parent-label (native-parent Head Labels) Label,
    Line is "  " ^ Key ^ " : " ^ Label ^ Mode, coq.say Line.

  pred registration-label i:view-registration, o:string.
  registration-label explicit-view "explicit".
  registration-label coercion-view "Coercion".
  registration-label canonical-view "Canonical".
  registration-label coercion-canonical-view "Coercion, Canonical".

  pred print-view i:struct-conversion.
  print-view (conversion _ _ Ref Registration) :-
    coq.gref->id (const Ref) Name,
    registration-label Registration Label,
    Line is "  " ^ Name ^ " [" ^ Label ^ "]",
    coq.say Line.

  pred print-packer i:constant.
  print-packer Ref :-
    coq.gref->id (const Ref) Name,
    Line is "  " ^ Name,
    coq.say Line.

  pred print-export i:(pair inductive (list id)).
  print-export (pr Export Keys) :-
    coq.gref->id (indt Export) Name,
    Line is "  " ^ Name ^ " [" ^ {std.string.concat ", " Keys} ^ "]",
    coq.say Line.

  pred parent-label i:struct-parent, o:id.
  parent-label (native-parent sort-head []) "Type".
  parent-label (native-parent (ref-head Ref) Args) Label :-
    coq.gref->id Ref Head, std.string.concat " " [Head | Args] Label.
  parent-label (named-parent I Args) Label :-
    coq.gref->id (indt I) Head, std.string.concat " " [Head | Args] Label.

  pred print-struct i:list struct-parent, i:id, i:list id, i:list inductive, i:list component,
      i:list struct-conversion, i:list constant, i:list (pair inductive (list id)),
      i:list (pair constant (list id)).
  print-struct Declared Name Params Parents Cs Views Packers Exports Assemblies :-
    std.map Declared parent-label Names,
    Title is "Minks structure " ^ Name,
    coq.say Title,
    if (Params = []) true (coq.say "Parameters:" Params),
    if (Names = []) (coq.say "Direct parents: none")
      (Line is "Direct parents: " ^ {std.string.concat ", " Names},
       coq.say Line),
    coq.say "Packed fields:",
    std.forall Cs (c\ sigma mode\
      if (c = slot _ (native-kind _) _) (mode = " [Coercion]")
        (if (auto-instance Cs c) (mode = " [instance]") (mode = " [explicit]")),
      print-slot Parents mode c),
    if (Views = []) true (coq.say "Conversions:", std.forall Views print-view),
    if (Packers = []) true
      (coq.say "Packing functions:", std.forall Packers print-packer),
    if (Exports = []) true
      (coq.say "Relative interfaces:", std.forall Exports print-export),
    if (Assemblies = []) true (
      coq.say "Assembled views:",
      std.forall Assemblies (a\ sigma ref keys label line\
        a = pr ref keys, coq.gref->id (const ref) label,
        line is "  " ^ label ^ " [" ^ {std.string.concat ", " keys} ^ "]",
        coq.say line)).
}}.
