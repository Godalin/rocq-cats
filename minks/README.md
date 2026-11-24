# Minks

Minks generates flat, universe-polymorphic Rocq structures from registered
mixins. The independent Dune package is `rocq-minks`. Import
[`Minks.all`](theories/all.v) to use its three commands.

**Core principle.** The semantic model is the selected components and their
dependencies in a given parameter context. A mixin adds operations or laws
over its dependencies. A structure packs the selected components, and an
export fixes part of that structure and presents the rest as a relative
interface. Generated Rocq declarations preserve which component supplies
each dependency.

The [rule audit](doc/implementation-audit.md) compares the formal specification
with the generator and its executable examples.

## Quick start

```coq
From Minks Require Import all.

Minks.Mixin HasPoint {A : Type}
  :=
  { point : A }.

Minks.Mixin HasSecondPoint (A : Type)
  extends HasPoint (A := A)
  :=
  { second_point : A }.

Minks.Struct Pointed
  extends Type
  with  hasPoint : HasPoint [carrier].

Minks.Struct TwoPoints
  extends Pointed
  with  hasSecondPoint : HasSecondPoint [carrier, hasPoint]
  exports HasTwoPoints [carrier],
          HasSecondPointOn [hasPoint].

Minks.Inspect TwoPoints.
```

`HasSecondPoint` takes `A` and an implicit `HasPoint` witness. `TwoPoints`
stores one carrier and those two selected mixins. `HasTwoPoints` fixes only
the carrier, while `HasSecondPointOn` fixes the carrier and the first point.

## Command reference

### `Minks.Mixin`

```text
Minks.Mixin Name binders
  [extends ParentApplication, ...]
  [: ResultSort]
  := [Constructor] { fields }.
```

- **Declaration.** The command defines a Rocq typeclass and records its
  direct parent mixins, ordinary parameters, and the arguments of each
  inherited witness. The body uses Rocq class fields and their usual
  attributes.
- **Parent applications.** Each parent must be a registered mixin or a
  relative interface exported by `Minks.Struct`. Declare
  the child's ordinary parameters in its header or the enclosing section.
  Supply any Rocq term of the expected type, using header binders, section
  variables, and witnesses or local views introduced by earlier parents.
  For example, in `extends HasPoint nat, AtValue point`, the second parent
  can use the point selected by the first. A later parent cannot supply an
  earlier argument. Pass explicit arguments by position
  and implicit ordinary arguments by name, as in
  `Parent (A := option A) (fun x => x)`. The child uses the explicitness of its own
  binders at call sites. `extends` accepts these parent applications with
  optional universe instances. `@Parent` is unsupported.
- **Inherited witnesses.** Minks inserts the direct and transitive parent
  witnesses as implicit typeclass parameters. Read parents from left to right. Repeating a direct
  parent and reaching it through several paths both share one compatible
  witness. Match by mixin and key, then let Rocq check the selected witness
  at every required application, including indices with transparent aliases.
  Distinct explicit keys keep distinct witnesses. An unkeyed occurrence
  with multiple candidates is ambiguous. A unique candidate with an
  incompatible type rejects the declaration.
- **Relative parents.** Supply the fixed parameters of an exported class as
  ordinary arguments. Minks visits its remaining fields in constructor
  order and inserts their component witnesses. The selected dependency
  arguments and keys determine which other inherited witnesses are shared.
  Distinct component keys within the export remain distinct. The class
  body can refer to the assembled value by the usual lower-initial parent
  name, such as `hasMonoid` for `HasMonoid`. This local definition uses the
  exported constructor and adds no argument at call sites.
- **Parameter order.**
  1. Emit all binders written in the child's header, in their declared order
     and with their original explicitness. If a header binder needs a chosen
     structure, declare that choice earlier in the header or enclosing section.
  2. Read parents from left to right. For each parent, visit its inherited
     witnesses and then its own witness. For a relative parent, visit its
     remaining components instead.
  3. Append each inherited entry once all its inherited dependencies are
     in scope. Among ready entries, prefer shared entries and break ties
     by first encounter.
- **Universes.** The declaration uses Rocq's universe-polymorphism setting
  and universe syntax. An explicit universe declaration on the child
  fixes its universe parameter order. An explicit parent instance, such as
  `HasEquiv@{u e} A`, supplies the levels to use for that parent. Explicit
  instances for a shared witness must agree wherever both paths specify a
  level. Rocq infers the remaining levels and constraints.
- **Sections.** Inside a section, a parent application can name a visible
  section assumption. At each `End`, Rocq generalizes the assumptions used
  by the class, including those used by its inherited witness types.
  They become ordinary parameters before the previous binders, including
  assumptions whose types are registered mixins. Only the declaration's
  `extends` clause supplies direct parents. Subsequent applications read
  the Rocq type and implicit arguments for all ordinary binders. For example, a section `Context {A : Type}` can introduce
  a parent argument that is later supplied as `(A := B)`. Nested sections
  discharge one at a time. Importing the module preserves this information.
- **Output.** Use `Minks.Inspect Name.` to see the direct dependencies and
  the full parameter order. Positions shown in a dependency's argument list
  are zero-based indices into that order.

### `Minks.Struct`

```text
Minks.Struct Name binders
  [extends Parent ordinaryArg ..., ...]
  [with entry, ...]
  [exports Interface [parameterKeyOrStructure, ...], ...].
```

Each clause is optional and accepts a comma-separated list. The clauses
appear in the order shown. The brackets around a clause above indicate
optional syntax. The key lists inside `with` and `exports` use literal
square brackets.

#### Fields and dependencies

- **Parent layout.** A registered Minks parent contributes its instantiated
  fields. The first use of a native head `B` generates a Minks record
  `BCarrier` in the current module and registers it by Rocq identity.
  `extends B args` applies that base to the given arguments. Its sole
  field, `carrier`, contains a native value directly. `extends Type` uses
  `TypeCarrier`. Later declarations reuse the visible base, which is available
  to `Minks.Inspect` and explicit parent applications. Two independently
  imported bases for one native head require a qualified parent choice.
  Rocq rolls back the generated base if the declaration fails.
  Every registered structure, including a generated base, records one
  identity entry per field. Inheritance and inspection reject missing or
  inconsistent entries. An empty structure records an empty table.
  An empty parent list contributes zero fields.
- **Component identity.** A `with` entry can name a mixin declared with
  `Minks.Mixin` or an exported relative interface. A key
  identifies a slot for a direct mixin in the combined hierarchy.
  Each written key must be fresh among inherited fields, available local
  fields and earlier entries in the same declaration. Different keys may
  select independent witnesses of the same class. Parents still share
  compatible fields by key.
- **Projections.** The default name is `Name_key`. The form
  `key as projection : Mixin` names the projection of the new entry.
  Dependencies, exports and freshness checks use the original key.
- **Renaming a key.** `old as new` changes the public key of the same field.
  Later entries, exports and descendants use `new`. The old spelling is
  reserved on this branch. A parent view still reads the field through
  its original projection. When parents share a field, an explicitly
  renamed spelling wins over its original in either parent order. Among
  competing renamed spellings the first parent wins. All other spellings
  remain reserved. Unrelated fields cannot claim a renamed or retired key.
- **Field and constructor order.**
  1. Visit direct parents from left to right. Traverse each parent's
     flattened fields in order and merge matching keys. Place components
     common to two or more direct parents before the other inherited
     components, keeping their first-encounter order within each group.
  2. Append any new `with` components in declaration order. `MakeName` takes
     these fields in the resulting order.
- **Argument resolution.** At a `with` entry, the available fields are
  the inherited fields, and the preceding entries in `with`.
  A bracketed argument list can also name a visible section assumption.
  A name shared by an assumption and a field is ambiguous. Omitted lists
  search fields only. A bracketed argument list specifies every argument of the mixin in the
  order shown by `Minks.Inspect`, including implicit witnesses. An ordinary
  parameter can use any available field of the right type. A mixin witness
  must also match the registered mixin and the dependency keys selected for
  its earlier arguments. With brackets omitted, Minks checks the candidate
  lists in Rocq. It selects the unique well-typed list. With no match the
  command reports missing arguments, and with several it asks for explicit
  keys.
- **Instances.** In packed field order, the first projection of each
  class head is an instance at priority 1. All keys remain accessible by
  name. For example, if zero precedes one, search for a point selects zero.
  Field selection during declaration still checks for ambiguity.
- **Universes.** The packed record is universe-polymorphic. For a native
  carrier, its local universe levels come first in their original order,
  with unified levels listed once. Rocq checks the generated fields and
  infers the remaining universe levels, their order, and constraints.

#### Ordinary parameters in headers and sections

- The header gives the record's full parameter telescope in declaration
  order. For example, `Minks.Struct Tagged (A : Type)` retains `A`
  even when every field is independent of it. Parentheses declare explicit
  inputs and braces declare implicit inputs. Minks elaborates parent and
  field applications in this local binder context. Rocq generalizes used enclosing
  section assumptions before the header. A relative class takes the ambient
  inputs it uses; packing back into the record takes all its indices.
  `Minks.Inspect` reads the ordinary parameters and field arguments from
  the discharged constructor. In field lists, `param:B` refers to the
  ordinary binder `B`.
- In a later section, `extends LabelledPoint D` instantiates a discharged
  parent at the visible input `D`. Pass explicit parameters by position
  and implicit ones by name, as in `extends HeaderMap T x (A := X)`.
  Each argument can be a Rocq term, as in `extends Chosen (values L)`.
  This convention also applies to native parents. Rocq elaborates the
  application with the expected argument types and available coercions.
  Direct and transitive parent views use the same substitution. Two paths
  to the same declared ancestor must agree on its inputs.
- A relative export can be reused after discharge. For example,
  `with [e, p, label] : LabelledOn [D, carrier]` takes the new ordinary argument
  before the original fixed field. In a mixin declaration the corresponding
  parent application is `extends LabelledOn D A`.

#### Conversions and packing

- **Declared ancestors.** Minks generates a transparent `NameToAncestor`
  for every distinct Minks ancestor, in depth-first order starting with the
  listed parents. Each function packs the ancestor from the child's stored
  components. The record also computes each distinct direct parent in an
  anonymous definition at its declared arguments. This preserves Section
  dependencies even for an empty parent layout. Only stored components
  contribute keys and constructor arguments. The native carrier projection
  supplies the view to the native base. A public ancestor function can use
  a fresh target universe instance whenever its components typecheck there.
- **Constructing values.** Use the generated constructor or a direct-parent
  packing function, such as `MakeMagma` or `SemigroupOfMagma`. In Rocq 9.3,
  a record literal (`{| ... |}`) is rejected when the record contains an
  anonymous definition, even if the literal supplies every stored field.
- **Coercions.** Among the generated ancestor functions, Minks registers
  those to directly listed Minks parents. Rocq can follow the resulting
  coercion paths to more distant ancestors.
- **Canonical Structures.** A generated view to a declared Minks ancestor
  is also canonical when every automatically registered component instance
  of that ancestor keeps the same default key in the new structure. This lets
  Rocq infer the ancestor from a known projection while preserving
  explicit choices such as two selected points.
- **Views inferred from fields.** The command also compares the new
  structure with previously declared structures in the same module.
  Compatible layouts get a named view from the
  strictly larger component set to the smaller one when the conversion
  typechecks and the name is available. Either structure can have been
  declared first. Such inferred views are explicit.
- **Packing from a parent.** Each directly listed Minks parent gets a
  transparent `NameOfParent`. The function takes the parent first, then
  takes the components missing from that parent in `MakeName` field order.
  Their types refer to the specific fields of the supplied parent. Pack
  from distant ancestors by composing these functions. Minks generates
  the packers in ancestor traversal order, filtered to direct parents.
  For a native base,
  `MakeName` already takes the base followed by the required components.
- **Universe arguments.** Generated conversion and packing functions are
  universe-polymorphic. Rocq infers their universe parameters and constraints
  from the function types and bodies. A parent conversion can therefore
  have an independent result level when repacking its components permits it.

#### Relative interfaces with `exports`

- **Selection.** Each listed interface is generated from the same packed
  field list, in `exports` declaration order. A bare export fixes the keys shared by
  all direct parents. With one parent it fixes that parent's entire layout;
  with zero parents it fixes zero keys. Brackets select the given keys and
  their transitive dependencies. An explicit `[]` fixes zero fields.
  Authors choose the interface name. The fixed selections determine its shape.
- **Packed base.** A selection can include one Minks structure whose
  field keys, mixins, and dependencies match those of the exported
  structure. A declared ancestor or a structurally contained record can
  serve as this base. Its fields come from its projections.
  Field keys can appear before or after the base name. A field key already
  supplied by the base is an error. Dependencies of the additional fixed
  fields can use any of the base's projections.
- **Generated class and order.**
  1. Make the fixed fields explicit class parameters. Their order is the
     packed field order restricted to the fixed keys.
     With a packed base, its record is the first
     parameter and the fields it supplies are omitted from the parameter
     list. For example, `IsMonoidWithPoint [hasPoint, Magma]` takes a `Magma`
     followed by its selected point. The remaining fields provide associativity
     and the two unit laws for that point.
  2. Keep each remaining component as an individual field, in its original
     relative order. The constructor is `MakeInterface` and its arguments
     are the fixed parameters followed by these fields.
  3. Register the record as a Rocq typeclass. Field projections have names
     `Interface_key` and infer the fixed parameters from the instance.
     A remaining mixin projection is an instance at priority 2 if its key
     is the first of that class head in the original packed order. If the
     first key is fixed, the other keys stay explicit. These projections
     supply class arguments. Coercions to mixin classes require an explicit
     registration. Native carrier projections retain their coercion.
- **Universes.** The interface follows the packed record's universe order
  rule. A native carrier's local levels come first in their original
  order. Rocq infers the remaining levels, their order, and constraints.
- **Extraction and reassembly.** `NameToInterface` takes a packed `Name`
  and reads its exact fields. `NameOfInterface` takes the fixed parameters
  in class parameter order and then the interface value. It uses both to
  reconstruct `Name`. Both functions are transparent. Extraction is also
  an instance at priority 1 when a fixed index reads a field of the source
  or uses a declared ancestor view. An empty selection and a lone
  structurally matched, undeclared base leave extraction explicit.
  Reassembly is an explicit function.
  The resulting field projections reduce to the supplied choices. An
  equality of whole records may need a record case split. With a packed
  base, extraction uses the corresponding structure view and reassembly
  starts from that base's projections.
- **Composition metadata.** Every export also registers a virtual mixin.
  With a packed base, its first fixed input is the record itself, followed
  by any separately fixed components. Both `extends IsMonoid M` and
  `with : IsMonoid [M]` read the carrier, equivalence and operation
  from that same magma. The former binds the associativity, point and unit
  witnesses. The latter introduces those three fields in export order. Fixing the point as well leaves just the
  two law witnesses. Section parameters precede the fixed inputs after
  discharge.
- **Independent exports.** Declaring an interface registers its class and
  mixin metadata, its eligible field instances and its own extraction.
  It generates no maps, instances or coercions between exports, including
  exports of a parent and child. A client can define a view using named
  projections and register the desired direction locally.
- **Binding an export in `with`.** The brackets after the interface name
  supply its fixed inputs in order. Omitting them requests unique inference.
  The brackets before the colon bind its remaining fields in export order:
  1. `: E` uses the original exported keys. `[a, b] : E` supplies new keys.
     Each must be fresh. Every remaining field gets one key, even for a
     one-field export. An empty export takes an empty list or no list.
  2. `[a, b] as [p, q] : E` also names the two Rocq projections. Omitting
     `as` gives `Name_a` and `Name_b`. Both lists have the length of the
     remainder. A single identifier before the colon is reserved for a
     primitive mixin.
  3. Later components of the batch depend on the corresponding new fields.
     For example, in `Rng` the commutativity witness of `HasAbGroup` uses
     the new addition even though multiplication has the same type.
     [Ring example](examples/Algebra.v)
- **Inspection.** `Minks.Inspect Name` lists its current field keys, retired
  spellings, parent views and relative interfaces.
  `Minks.Inspect Interface` shows the fixed keys and expanded components
  and generated views for a field-key export, or the packed base and
  its additional fixed and remaining components for a packed-base export.
  `Print Interface.` displays the generated record and `Print Typeclasses.`
  shows its typeclass registration.

### `Minks.Inspect`

- **Input.** Supply the name of a mixin or packed structure previously
  declared by Minks.
- **Mixin output.** The command lists direct dependencies and ordered parameter metadata.
- **Structure output.** The summary lists the resolved parents, including generated native bases.
  It reports fields in packed order, selected dependency keys, inherited sources,
  and instance status. It also lists conversions and
  their registrations, packing functions, and relative interfaces.
- **Output.** Successful mixin and structure declarations are silent by default.
- **Effect.** The command reads the existing declarations and metadata.

## Build and run the examples

Use Rocq 9.3 or later, Rocq-Elpi 3.5.1 or later, and Dune 3.23 or later.
The examples use Stdlib 9.2 or later. From this directory, build and test
with the project switch.

```sh
opam exec --switch=rocq-cats -- dune build
opam exec --switch=rocq-cats -- dune runtest
```

The local `dune-workspace` makes `minks/` a build root. The Cats workspace
can build the same package from the repository root. `dune build @install`
prepares the package artifacts, and `opam install --switch=rocq-cats .`
installs the package into the switch when run from this directory. The
examples are built by `@runtest`.

For an editor session with an uninstalled local build, launch VsRocq from
the same workspace root so Dune supplies the local library path.

```sh
opam exec --switch=rocq-cats -- dune exec -- vsrocqtop
```

[`_CoqProject`](_CoqProject) maps the built theories and loads Elpi in the
editor session. The examples cover dependent components and generated
views in [Algebra](examples/Algebra.v) (magmas through commutative rings),
[Closure](examples/Closure.v), and [Lattice](examples/Lattice.v), with focused tests in
[Commands](examples/Commands.v), [Sections](examples/Sections.v) and
[Universes](examples/Universes.v).
Use `Set Printing Universes.` before `Print` to examine inferred
universe instances and constraints.
