# Minks

Minks generates flat, universe-polymorphic Rocq structures from registered
mixins. The independent Dune package is `rocq-minks`. Import
[`Minks.all`](theories/all.v) to use its three commands.

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
  Supply each ordinary parent argument using a visible parameter name. Pass explicit arguments by
  position and implicit ordinary arguments by name,
  as in `Parent (A := A) f`. The child uses the explicitness of its own
  binders at call sites. `extends` accepts these parent applications with
  optional universe instances. `@Parent` is unsupported.
- **Inherited witnesses.** Minks inserts the direct and transitive parent
  witnesses as implicit typeclass parameters. Paths share a witness when
  the referenced mixin and its selected argument list agree. Incompatible
  selections for the same mixin produce an error.
- **Relative parents.** Supply the fixed parameters of an exported class as
  ordinary arguments. Minks visits its remaining fields in constructor
  order and inserts their component witnesses. The selected dependency
  arguments and keys determine which other inherited witnesses are shared.
  Distinct component keys within the export remain distinct. The class
  body can refer to the assembled value by the usual lower-initial parent
  name, such as `hasMonoid` for `HasMonoid`. This local definition uses the
  exported constructor and adds no argument at call sites.
- **Parameter order.**
  1. Read parents from left to right. For each parent, visit the witness
     parameters in their declared order, then the parent witness itself.
     For a relative parent, visit its remaining components instead.
  2. Among witnesses whose witness inputs are ready, emit shared witnesses
     first. Break ties by first encounter.
  3. Insert each witness once its arguments are in scope. Ordinary
     parameters retain the child's order even when witnesses occur between
     them. Ordinary parameters left over after the last witness follow it.
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
- **Output.** A successful declaration prints its direct dependencies and
  the full parameter order. Positions shown in a dependency's argument list
  are zero-based indices into that order.

### `Minks.Struct`

```text
Minks.Struct Name
  [extends Parent ordinaryArg ..., ...]
  [with key [as projection] : Mixin [argumentKey, ...], ...]
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
  An empty parent list contributes zero fields.
- **Component identity.** A `with` entry can name a mixin declared with
  `Minks.Mixin` or an exported relative interface. A key
  identifies a slot for a direct mixin in the combined hierarchy.
  Repeated occurrences of a key merge when the referenced mixin and its
  ordered dependency keys agree. Different keys can store independent
  witnesses of the same mixin. A conflicting definition of one key is an
  error.
- **Projections.** The default name is `Name_key`. The form
  `key as projection : Mixin` changes the generated projection name.
  Dependency lists, inheritance, and exports continue to use the key.
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

#### Structures declared in sections

- Define a structure in a Rocq section to make its used assumptions ordinary
  parameters. Its constructor, projections, forgetful views, packing functions
  and relative interfaces acquire the inputs they use at each `End`.
  `Minks.Inspect` reads the ordinary parameters and field arguments from
  the discharged constructor. In field lists, `param:B` refers to the
  ordinary binder `B`.
- In a later section, `extends LabelledPoint D` instantiates a discharged
  parent at the visible input `D`. List its parameters in Rocq binder order.
  Direct and transitive parent views use the same substitution. Two paths
  to the same declared ancestor must agree on its inputs.
- A relative export can be reused after discharge. For example,
  `with chosen : LabelledOn [D, carrier]` takes the new ordinary argument
  before the original fixed field. In a mixin declaration the corresponding
  parent application is `extends LabelledOn D A`.
- The current structure command takes ordinary inputs from enclosing sections.
  Structure headers with explicit binders and named implicit arguments in
  structure parent applications remain open parts of the formal specification.

#### Conversions and packing

- **Declared ancestors.** Minks generates a transparent `NameToAncestor`
  for every distinct Minks ancestor, in depth-first order starting with the
  listed parents. Each function reconstructs the ancestor from the fields
  already stored in `Name`. The native carrier projection supplies the
  view to the native base.
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
  universe-polymorphic. Rocq infers their universe parameters, order, and
  constraints from their checked types and bodies.

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
  `with laws : IsMonoid [M]` read the carrier, equivalence and operation
  from that same magma. The former binds the associativity, point and unit
  witnesses. The latter reuses or stores those witnesses and builds
  `laws : IsMonoid M` from them. Fixing the point as well leaves just the
  two law witnesses. Section parameters precede the fixed inputs after
  discharge.
- **Independent exports.** Declaring an interface registers its class and
  mixin metadata, its eligible field instances and its own extraction.
  It generates no maps, instances or coercions between exports, including
  exports of a parent and child. A client can define a view using named
  projections and register the desired direction locally.
- **Assembly in `with`.** The argument list of `with key : Interface`
  selects the fixed parameters in order. With the list
  omitted, Minks looks for a unique fixed selection among available
  fields. It then matches the remaining components in constructor order:
  1. Match the registered mixin and its dependency keys after mapping the
     earlier arguments to the selected fields. Prefer a compatible field
     with the original key. Each component in the interface has a distinct
     selected field, even when several components have identical types.
  2. Reuse a unique full match. If none exists, reuse the unique matches
     encountered in order and append missing fields under their original
     keys. Ambiguous matches and conflicting keys produce an error.
  3. Generate a transparent `Name_key` view assembling the class from
     those fields. `as projection` changes the view name. If it coincides
     with a default physical projection name, the physical projection
     gets a `_component` suffix. The view is called explicitly and is
     not a selectable field key.
- **Inspection.** `Minks.Inspect Name` lists each interface with the actual
  fixed key list and each assembled view with its selected keys.
  `Minks.Inspect Interface` shows the fixed keys and expanded components
  and generated views for a field-key export, or the packed base and
  its additional fixed and remaining components for a packed-base export.
  `Print Interface.` displays the generated record and `Print Typeclasses.`
  shows its typeclass registration.

### `Minks.Inspect`

- **Input.** Supply the name of a mixin or packed structure previously
  declared by Minks.
- **Mixin output.** The direct dependencies and ordered parameter metadata
  use the same format as the declaration summary.
- **Structure output.** The summary lists the resolved parents, including generated native bases.
  It reports fields in packed order, selected dependency keys, inherited sources,
  and instance status. It also lists conversions and
  their registrations, packing functions, and relative interfaces.
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
