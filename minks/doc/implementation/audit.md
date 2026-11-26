# Minks implementation audit

The audit began with [the formal specification](../formal-semantics.pdf) at
`7b93e6e` and includes subsequent Section and module changes on
`minks-development-48`. The examples check individual declarations on Rocq 9.3.

## Parent order and witness sharing

An ordinary parent supplies an unkeyed `HasFlag`. A virtual parent supplies
`leftFlag` and `rightFlag` of that class. All three have empty argument lists.

| Visit order | Witness-Share result |
| --- | --- |
| unkeyed, left, right | Left shares the first entry; right starts another. The flags compute to (true, false). |
| left, right, unkeyed | The last occurrence has two candidates. The declaration fails before binder ordering. |

Determinacy assumes a fixed parent order. Collecting named keys before
resolving unkeyed occurrences would reject both orders under the current
ambiguity check. Such a change would affect accepted declarations and
dependencies whose argument identities are still being resolved.
[Sharing.v](../../tests/Sharing.v)

## Relative interfaces

- **With-Assembly.** A diagonal pair selects the flag introduced in its batch
  even with two older flags in scope. A ring similarly selects addition.
  Argument diagnostics distinguish available fields from parameters and show
  competing selections under the names visible at the entry.
  [Commands.v](../../tests/Commands.v)
  [Sharing.v](../../tests/Sharing.v)
- **Export-Fix.** Fixing `hasMagma` fixes carrier, equivalence and multiplication
  in order. Fixing packed `Magma` gives a different telescope. Both recover
  the supplied point by reduction; repeated keys fail. [Sharing.v](../../tests/Sharing.v)
- **Fix-Compose.** For an arbitrary monoid, fixing its magma and then its
  selected point gives the same point, associativity witness and unit-law
  witness by conversion as fixing both directly. On an arbitrary ring, the
  two staged exports recover the stored additive and multiplicative unit laws;
  exchanging their point indices fails. The general statement for nested
  closed selections remains open. [AlgebraChecks.v](../../tests/AlgebraChecks.v)
- **Export-Common.** The bare export of a `LabelledSort` child fixes both
  inherited fields and fails because none remain; `[]` takes both as constructor arguments. A parentless
  structure has no inherited fields to fix. [NativeParents.v](../../tests/NativeParents.v)
- **Expansion.** At the same universe instance, `HasMonoid A` and the ordered
  parents `IsSemigroup A, IsUnitAt A` give convertible mixin parameter types.
  The struct constructors take convertible fields in the same order and
  recover the same witnesses. Reversing the parents puts the point and its
  laws before associativity. The fixed-magma case compares fields on its
  projected carrier. Each declaration retains its own type and parents.
  [Presentations.v](../../tests/Presentations.v)

## Rule coverage

| Rules | Implementation and evidence | Coverage or outstanding obligation |
| --- | --- | --- |
| WF-Decl, WF-Extends, Mixin-Ext, Parent-Scan | [Mixin grammar](../../plugin/g_minks.mlg), [parameter construction](../../plugin/mixin_parameters.ml), [Sections.v](../../tests/Sections.v) | Parent applications take Rocq terms. [Sharing.v](../../tests/Sharing.v) checks convertible applications in both commands and rejects ill-typed arguments. Mixin inheritance inserts witnesses. [NativeParents.v](../../tests/NativeParents.v) checks dependent and unused Struct header indices, named implicit parent arguments, function coercions, and the generated parent and relative maps. |
| Input-Name, Args-Check, WF-With, Args-Infer, WF-Omit | [Struct.v](../../theories/Struct.v), [Sections.v](../../tests/Sections.v) | Explicit arguments distinguish ambient inputs from field keys. Omitted tuples are enumerated over fields and checked by Rocq. The completed declaration is checked again. |
| Univ-Inst, Struct-Univ, Univ-Assemble | [native record declaration](../../plugin/packed_record.ml), [parameter construction](../../plugin/mixin_parameters.ml), [Universes.v](../../tests/Universes.v) | Tests exercise open and closed mixin universe binders, shared levels and conflicting instances. Handwritten and generated records agree on an inferred field bound, an incompatible field instance, and a strict constraint supplied only by the header. |
| Witness-Share, Binder-Order | [parameter construction](../../plugin/mixin_parameters.ml), [Sharing.v](../../tests/Sharing.v), [Commands.v](../../tests/Commands.v) | The examples cover keyed and unkeyed sharing, repeated direct parents, and inherited exports indexed by convertible functions. Incompatible indices fail even when the body ignores the witnesses. Among ready witnesses the implementation prioritizes shared entries. All declared header binders precede the inherited entries. |
| Key-New, Key-Reuse, Parent-Inst | [Registry](../../plugin/component_keys.ml), [NativeParents.v](../../tests/NativeParents.v), [Sharing.v](../../tests/Sharing.v) | Named keys include their declaring module. [Commands.v](../../tests/Commands.v) exercises qualified lookup, reuse, and independent same-name witnesses. Key reuse checks the whole ordinary telescope and the selected dependency identities. Independent views preserve renamed fields by conversion. Repeating a parent argument keeps both selected points and the path based at the first. |
| Parent-Union, Ancestor-Agree, Struct-Pack | [Spec.v](../../theories/Spec.v), [Struct.v](../../theories/Struct.v), [Sections.v](../../tests/Sections.v) | Parent applications specialize inherited components. Rocq conversion checks the elaborated inputs of a shared ancestor. Packing partitions inherited fields into shared and remaining lists. Native parents contribute ordinary layout entries. Empty parents contribute zero fields. [NativeParents.v](../../tests/NativeParents.v) checks that a native type and its transparent alias share one field, including for a polymorphic family at the same index. Distinct variable indices are rejected. |
| Expand-Field, With-Assembly | [Struct.v](../../theories/Struct.v), [Spec.v](../../theories/Spec.v), [Sharing.v](../../tests/Sharing.v) | Both export forms bind the remaining fields in order, substitute earlier selections and check the constructor application. Tests cover key and projection arity and duplicate keys. |
| Export-Fix, Export-Common, Export-Form, Export-To, Export-Of | [Relative.v](../../theories/Relative.v), [Algebra.v](../../examples/Algebra.v), [Sharing.v](../../tests/Sharing.v) | Selection closure and transparent extraction and packing work in the examples above. Packed-base exports register the same virtual mixin interface as field-key exports. The regressions extend and assemble `IsMonoid M`, check its selected point, and reject duplicate batch keys. [Sections.v](../../tests/Sections.v) also exercises projections of a parameterized packed base. [ViewMatch.v](../../tests/ViewMatch.v) checks an independent packed base with permuted indices and a renamed field. [Commands.v](../../tests/Commands.v) rejects distinct module keys with identical names and types. |
| Parent-To, Parent-Of, Projection-Name | [Flat.v](../../theories/Flat.v), [Struct.v](../../theories/Struct.v), [Algebra.v](../../examples/Algebra.v) | Declared ancestor maps rebuild selected fields. Direct-parent packers take missing components. [Commands.v](../../tests/Commands.v) rejects repeated and inherited keys even with a projection alias, and checks that a fresh key stores a second witness of the same class. |
| WF-Compare, View-Match, View-Explicit | [Flat.v](../../theories/Flat.v), [Relative.v](../../theories/Relative.v), [Commands.v](../../tests/Commands.v) | Discovery checks strict component inclusion and checks the candidate term with Rocq. Export declarations generate no inter-interface views. Target indices are inferred from aligned descriptors. [ViewMatch.v](../../tests/ViewMatch.v) checks both declaration orders for an independent three-key layout, reordered indices after parent instantiation, and a missing target index. A packed export and its view also mix a section assumption with a header parameter and drop the unused section assumption at discharge. The resulting views reduce to the original projections. The same test checks discovery after nested discharge, preservation of an occupied view name, and retry after a later export rejects the command. |
| Coerce-Parent, Inst-Field, Inst-Export, Canon-View | [Flat.v](../../theories/Flat.v), [Relative.v](../../theories/Relative.v), [Commands.v](../../tests/Commands.v) | Direct declared parents request coercions. Field registration selects the first key for each class head. Canonical views preserve those keys. Anchored exports register an extraction instance. Global inference coherence remains open. |
| Section-End | [mixin parameter roles](../../theories/Spec.v), [Sections.v](../../tests/Sections.v), [Commands.v](../../tests/Commands.v) | Nested discharge, import, applied parent views and relative reassembly have executable cases. Preservation for every input used only by hierarchy metadata still needs an argument. |

The `RenamedKeys` module checks both orders of the ring diamond, competing
explicit renames, a packed-base export after a second rename, retired-key
rejection and persistence after section discharge. [AlgebraChecks.v](../../tests/AlgebraChecks.v)

[Commands.v](../../tests/Commands.v) checks positional `@Parent` applications,
shared and extra witness positions, explicit and implicit class parameters,
and Rocq's generalization of a free index in an anonymous instance binder.

## Proof obligations and research directions

1. **Formation.** Assume Rocq resolves references, types user terms, checks
   conversion and admits the universe constraints. Generated names must be
   fresh. Minks establishes scope, dependency closure, unique selections
   and agreement along parent paths.
2. **Generation.** Derive the types of classes, records, projections and
   parent and relative maps from a checked signature. Correct typing of
   generated bodies and reduction to the selected components are conclusions
   of Gen-Preserve. Rechecking an example establishes one instance.
3. **Registration.** Minks decides eligibility; acceptance depends on Rocq
   and the environment. Later Canonical and instance searches need their
   own coherence argument. Relative decomposition and Fix-Compose can be
   stated as fieldwise substitution theorems independently of search.

A translation to dependent records would track the key selected by each
projection, including fields of the same type. The proposed CwF interpretation
studies closed sublayouts and relative interfaces under substitution. The
proof method remains open. [Language specification](https://github.com/Godalin/rocq-cats/issues/50) ·
[Categorical interpretation](https://github.com/Godalin/rocq-cats/issues/51)

## Registration and module scope

Each export records its Rocq class, packed base, fixed and remaining
components, constructor and origin projections. A fixed field or ancestor
view identifying the source enables an extraction instance. Remaining mixin
fields provide instances for default keys. Reverse packers stay explicit.
Export-to-export views and the proposed Trans command are unimplemented.

In a local probe, registering assembly of `IsGroup` from `HasInverse`
alongside the inverse projection made search revisit the original goal when
no inverse was available, even without a canonical packer.

Mixin headers, packed layouts, relative interfaces and opened key names use
regular Elpi clauses. Inheritance, assembly and inspection share declaration
metadata indexed by Rocq reference, including after functor substitution.
Qualified lookup reads that data in a protected Rocq state. OCaml checks
contextual key descriptors by conversion and on Section discharge.
[Modules.v](../../tests/Modules.v) checks a qualified diamond before
import and after re-export.

## Source declaration metadata

Native record generation emits glob declarations for every named stored
projection, including inherited components, projection aliases and native
parent views. Authored names keep their source locations. A generated name
without a location uses the record name's range, or the current command's
range when the record name is also generated. Several declarations may
share that range. This fallback changes only glob output, not the record
syntax or generated terms. Export tools own any presentation remapping.
[Glob.v](../../tests/Glob.v) checks inherited, relative and native projection
computations; [glob_test.ml](../../tests/glob_test.ml) checks the raw
declarations, their uniqueness and their byte ranges without an export filter.
