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
[Sharing.v](../../examples/Sharing.v)

## Relative interfaces

- **With-Assembly.** A diagonal pair selects the flag introduced in its batch
  even with two older flags in scope. A ring similarly selects addition.
  [Sharing.v](../../examples/Sharing.v)
- **Export-Fix.** Fixing `hasMagma` fixes carrier, equivalence and multiplication
  in order. Fixing packed `Magma` gives a different telescope. Both recover
  the supplied point by reduction; repeated keys fail. Composition for
  arbitrary nested closed selections remains open. [Sharing.v](../../examples/Sharing.v)
- **Export-Common.** The bare export of a `LabelledSort` child fixes both
  inherited fields; `[]` takes both as constructor arguments. A parentless
  structure has no inherited fields to fix. [NativeParents.v](../../examples/NativeParents.v)
- **Expansion.** At the same universe instance, `HasMonoid A` and the ordered
  parents `IsSemigroup A, IsUnitAt A` give convertible mixin parameter types.
  The struct constructors take convertible fields in the same order and
  recover the same witnesses. Reversing the parents puts the point and its
  laws before associativity. The fixed-magma case compares fields on its
  projected carrier. Each declaration retains its own type and parents.
  [Presentations.v](../../examples/Presentations.v)

## Rule coverage

| Rules | Implementation and evidence | Coverage or outstanding obligation |
| --- | --- | --- |
| WF-Decl, WF-Extends, Mixin-Ext, Parent-Scan | [Mixin grammar](../../plugin/g_minks.mlg), [parameter construction](../../plugin/mixin_parameters.ml), [Sections.v](../../examples/Sections.v) | Parent applications take Rocq terms. [Sharing.v](../../examples/Sharing.v) checks convertible applications in both commands and rejects ill-typed arguments. Mixin inheritance inserts witnesses. [NativeParents.v](../../examples/NativeParents.v) checks dependent and unused Struct header indices, named implicit parent arguments, function coercions, and the generated parent and relative maps. |
| Input-Name, Args-Check, WF-With, Args-Infer, WF-Omit | [Struct.v](../../theories/Struct.v), [Sections.v](../../examples/Sections.v) | Explicit arguments distinguish ambient inputs from field keys. Omitted tuples are enumerated over fields and checked by Rocq. The completed declaration is checked again. |
| Univ-Inst, Struct-Univ, Univ-Assemble | [parameter construction](../../plugin/mixin_parameters.ml), [Flat.v](../../theories/Flat.v), [Universes.v](../../examples/Universes.v) | Tests exercise open and closed mixin universe binders, shared levels and conflicting instances. Struct headers accept explicit universe binders. |
| Witness-Share, Binder-Order | [parameter construction](../../plugin/mixin_parameters.ml), [Sharing.v](../../examples/Sharing.v), [Commands.v](../../examples/Commands.v) | The examples cover keyed and unkeyed sharing, repeated direct parents, and inherited exports indexed by convertible functions. Incompatible indices fail even when the body ignores the witnesses. Among ready witnesses the implementation prioritizes shared entries. All declared header binders precede the inherited entries. |
| Key-New, Key-Reuse, Parent-Inst | [Registry](../../plugin/component_keys.ml), [NativeParents.v](../../examples/NativeParents.v), [Sharing.v](../../examples/Sharing.v) | Named keys include their declaring module. [Commands.v](../../examples/Commands.v) exercises qualified lookup, reuse, and independent same-name witnesses. Key reuse checks the whole ordinary telescope and the selected dependency identities. Independent views preserve renamed fields by conversion. Repeating a parent argument keeps both selected points and the path based at the first. |
| Parent-Union, Ancestor-Agree, Struct-Pack | [Spec.v](../../theories/Spec.v), [Struct.v](../../theories/Struct.v), [Sections.v](../../examples/Sections.v) | Parent applications specialize inherited components. Rocq conversion checks the elaborated inputs of a shared ancestor. Packing partitions inherited fields into shared and remaining lists. Native parents contribute ordinary layout entries. Empty parents contribute zero fields. Matching still compares native heads and argument keys; general conversion of distinct native heads is open. |
| Expand-Field, With-Assembly | [Struct.v](../../theories/Struct.v), [Spec.v](../../theories/Spec.v), [Sharing.v](../../examples/Sharing.v) | Both export forms bind the remaining fields in order, substitute earlier selections and check the constructor application. Tests cover key and projection arity and duplicate keys. |
| Export-Fix, Export-Common, Export-Form, Export-To, Export-Of | [Relative.v](../../theories/Relative.v), [Algebra.v](../../examples/Algebra.v), [Sharing.v](../../examples/Sharing.v) | Selection closure and transparent extraction and packing work in the examples above. Packed-base exports register the same virtual mixin interface as field-key exports. The regressions extend and assemble `IsMonoid M`, check its selected point, and reject duplicate batch keys. [Sections.v](../../examples/Sections.v) also exercises projections of a parameterized packed base. |
| Parent-To, Parent-Of, Projection-Name | [Flat.v](../../theories/Flat.v), [Struct.v](../../theories/Struct.v), [Algebra.v](../../examples/Algebra.v) | Declared ancestor maps rebuild selected fields. Direct-parent packers take missing components. [Commands.v](../../examples/Commands.v) rejects repeated and inherited keys even with a projection alias, and checks that a fresh key stores a second witness of the same class. |
| WF-Compare, View-Match, View-Explicit | [Flat.v](../../theories/Flat.v), [Relative.v](../../theories/Relative.v), [Commands.v](../../examples/Commands.v) | Discovery checks strict component inclusion and checks the candidate term with Rocq. Export declarations generate no inter-interface views. General inference of a target family's parameter substitution from aligned descriptors is missing. |
| Coerce-Parent, Inst-Field, Inst-Export, Canon-View | [Flat.v](../../theories/Flat.v), [Relative.v](../../theories/Relative.v), [Commands.v](../../examples/Commands.v) | Direct declared parents request coercions. Field registration selects the first key for each class head. Canonical views preserve those keys. Anchored exports register an extraction instance. Global inference coherence remains open. |
| Section-End | [mixin parameter roles](../../theories/Spec.v), [Sections.v](../../examples/Sections.v), [Commands.v](../../examples/Commands.v) | Nested discharge, import, applied parent views and relative reassembly have executable cases. Preservation for every input used only by hierarchy metadata still needs an argument. |

The `RenamedKeys` module checks both orders of the ring diamond, competing
explicit renames, a packed-base export after a second rename, retired-key
rejection and persistence after section discharge. [Algebra.v](../../examples/Algebra.v)

## Planned syntax

- [ ] Let `extends @Parent A x` supply all ordinary parameters positionally,
  including implicit ones, in declaration order. With binders
  `{A : Type} (x : A)` this corresponds to `extends Parent (A := A) x`.
  Minks supplies any intervening inherited witnesses.

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
[Modules.v](../../examples/Modules.v) checks a qualified diamond before
import and after re-export.
