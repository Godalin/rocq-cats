# Minks implementation audit

The rule names refer to the [formal specification](formal-semantics.pdf)
at `7b93e6e`. The implementation reviewed here includes the subsequent
Section changes in the `minks-development-48` worktree. The executable
cases use Rocq 9.3. A successful example checks that particular declaration.

## Does permuting parents preserve acceptance?

For the current language the answer is **no**. Let an ordinary parent
contribute one unkeyed witness of class `HasFlag`. Let a virtual parent
contribute two fields of the same class with keys `leftFlag` and
`rightFlag`. All three occurrences have identical (empty) argument lists.

| Visit order | Table updates under Parent-Scan and Witness-Share | Outcome |
| --- | --- | --- |
| unkeyed, left, right | Insert the unkeyed witness. Left adopts its identity. Right starts a second entry. | Accepted. Setting the two flags to true and false computes the pair (true, false). |
| left, right, unkeyed | Insert each keyed witness. The third occurrence sees two eligible identities. | Rejected before emitting binders. |

This is deterministic for a fixed order. The specification's mixin
parameter determinacy obligation fixes the parent applications in order.
It therefore does not imply invariance under permutation. Binder-Order
only acts on the surviving table. Changing its tie-breaker cannot change
either outcome. A regression for both orders is in [Sharing.v](../examples/Sharing.v).

A possible future policy would collect the distinct named keys for each
head before resolving an unkeyed occurrence. One eligible key could absorb
it and several could require explicit selection. With the present rule
that tests ambiguity before argument agreement, both permutations above
would then be rejected. Adopting that policy requires a decision about
existing accepted declarations and about dependent occurrences whose
argument identities are themselves being resolved.

## Relative interfaces

- **With-Assembly.** The diagonal pair uses the new flag introduced in
  the same batch even with two older flags in scope. The algebra example
  checks the analogous dependency on addition in a ring. [Sharing.v](../examples/Sharing.v)
- **Export-Fix.** Selecting only `hasMagma` fixes the carrier,
  equivalence and multiplication in that order. Packing preserves the
  supplied point. Selecting the packed `Magma` gives a different input
  telescope and extracts the same point by reduction. Repeating a key
  is rejected. These are fieldwise instances of relative decomposition.
  General composition for arbitrary nested closed selections remains a
  proof obligation. [Sharing.v](../examples/Sharing.v)
- **Export-Common and the empty selection.** A child of `LabelledSort`
  exports both a bare interface and one with `[]`. The former fixes both
  inherited fields. The latter takes them as constructor fields. A
  parentless structure has no inherited field to fix.
  [NativeParents.v](../examples/NativeParents.v)

### Expanding an export or listing its components

[Presentations.v](../examples/Presentations.v) compares inheritance through
`HasMonoid A` with the ordered list `IsSemigroup A, IsUnitAt A`.
The generated mixin parameter types are convertible at the same universe
instance. Reversing the list moves the point and its unit laws before
associativity. The corresponding struct constructors have convertible
field types in the same order, and reading back the assembled monoid
computes to the same witnesses. The comparison also checks a relative
export on a fixed magma against its components on the projected carrier.
These checks concern the generated interfaces. Each declaration still
introduces its own Rocq type and records its declared parents.

## Rule coverage by implementation stage

The table distinguishes executable observations from source inspection.
A rule with an identified gap can still generate correct declarations on
the supported fragment.

| Rules | Implementation and evidence | Coverage or outstanding obligation |
| --- | --- | --- |
| WF-Decl, WF-Extends, Mixin-Ext, Parent-Scan | [Mixin grammar](../plugin/g_minks.mlg), [parameter construction](../plugin/mixin_parameters.ml), [Sections.v](../examples/Sections.v) | Parent applications take Rocq terms. [Sharing.v](../examples/Sharing.v) checks convertible applications in both commands and rejects ill-typed arguments. Mixin inheritance inserts witnesses. [NativeParents.v](../examples/NativeParents.v) checks dependent and unused Struct header indices, named implicit parent arguments, function coercions, and the generated parent and relative maps. |
| Input-Name, Args-Check, WF-With, Args-Infer, WF-Omit | [Struct.v](../theories/Struct.v), [Sections.v](../examples/Sections.v) | Explicit arguments distinguish ambient inputs from field keys. Omitted tuples are enumerated over fields and checked by Rocq. The completed declaration is checked again. |
| Univ-Inst, Struct-Univ, Univ-Assemble | [parameter construction](../plugin/mixin_parameters.ml), [Flat.v](../theories/Flat.v), [Universes.v](../examples/Universes.v) | Tests exercise open and closed mixin universe binders, shared levels and conflicting instances. Struct headers accept explicit universe binders. |
| Witness-Share, Binder-Order | [parameter construction](../plugin/mixin_parameters.ml), [Sharing.v](../examples/Sharing.v), [Commands.v](../examples/Commands.v) | The examples cover keyed and unkeyed sharing, repeated direct parents, and inherited exports indexed by convertible functions. Incompatible indices fail even when the body ignores the witnesses. Among ready witnesses the implementation prioritizes shared entries. All declared header binders precede the inherited entries. |
| Key-New, Key-Reuse, Parent-Inst | [Registry](../plugin/component_keys.ml), [NativeParents.v](../examples/NativeParents.v), [Sharing.v](../examples/Sharing.v) | Named keys include their declaring module. [Commands.v](../examples/Commands.v) exercises qualified lookup, reuse, and independent same-name witnesses. Key reuse checks the whole ordinary telescope and the selected dependency identities. Independent views preserve renamed fields by conversion. Repeating a parent argument keeps both selected points and the path based at the first. |
| Parent-Union, Ancestor-Agree, Struct-Pack | [Spec.v](../theories/Spec.v), [Struct.v](../theories/Struct.v), [Sections.v](../examples/Sections.v) | Parent applications specialize inherited components. Rocq conversion checks the elaborated inputs of a shared ancestor. Packing partitions inherited fields into shared and remaining lists. Native parents contribute ordinary layout entries. Empty parents contribute zero fields. Matching still compares native heads and argument keys; general conversion of distinct native heads is open. |
| Expand-Field, With-Assembly | [Struct.v](../theories/Struct.v), [Spec.v](../theories/Spec.v), [Sharing.v](../examples/Sharing.v) | Both export forms bind the remaining fields in order, substitute earlier selections and check the constructor application. Tests cover key and projection arity and duplicate keys. |
| Export-Fix, Export-Common, Export-Form, Export-To, Export-Of | [Relative.v](../theories/Relative.v), [Algebra.v](../examples/Algebra.v), [Sharing.v](../examples/Sharing.v) | Selection closure and transparent extraction and packing work in the examples above. Packed-base exports register the same virtual mixin interface as field-key exports. The regressions extend and assemble `IsMonoid M`, check its selected point, and reject duplicate batch keys. [Sections.v](../examples/Sections.v) also exercises projections of a parameterized packed base. |
| Parent-To, Parent-Of, Projection-Name | [Flat.v](../theories/Flat.v), [Struct.v](../theories/Struct.v), [Algebra.v](../examples/Algebra.v) | Declared ancestor maps rebuild selected fields. Direct-parent packers take missing components. [Commands.v](../examples/Commands.v) rejects repeated and inherited keys even with a projection alias, and checks that a fresh key stores a second witness of the same class. |
| WF-Compare, View-Match, View-Explicit | [Flat.v](../theories/Flat.v), [Relative.v](../theories/Relative.v), [Commands.v](../examples/Commands.v) | Discovery checks strict component inclusion and checks the candidate term with Rocq. Export declarations generate no inter-interface views. General inference of a target family's parameter substitution from aligned descriptors is missing. |
| Coerce-Parent, Inst-Field, Inst-Export, Canon-View | [Flat.v](../theories/Flat.v), [Relative.v](../theories/Relative.v), [Commands.v](../examples/Commands.v) | Direct declared parents request coercions. Field registration selects the first key for each class head. Canonical views preserve those keys. Anchored exports register an extraction instance. Global inference coherence remains open. |
| Section-End | [mixin parameter roles](../theories/Spec.v), [Sections.v](../examples/Sections.v), [Commands.v](../examples/Commands.v) | Nested discharge, import, applied parent views and relative reassembly have executable cases. Preservation for every input used only by hierarchy metadata still needs an argument. |

The `RenamedKeys` module checks both orders of the ring diamond, competing
explicit renames, a packed-base export after a second rename, retired-key
rejection and persistence after section discharge. [Algebra.v](../examples/Algebra.v)

## Planned syntax

- [ ] Support `extends @Parent` with positional arguments for all ordinary
  parameters, including implicit ones, in their declared order. Inherited
  mixin witnesses take no argument positions; Minks supplies them during
  inheritance. For a parent with ordinary parameters `{A : Type} (x : A)`,
  `extends @Parent A x` would select the same inputs as
  `extends Parent (A := A) x`, even with an inherited witness between them.

## Boundary of Gen-Preserve

A proof can separate three judgments.

1. **Formation.** Assume that Rocq resolves the input references, types the
   user terms under their supplied binders, decides the required
   conversions and admits the chosen universe constraints. Require fresh
   generated names. Minks must establish scope, dependency closure,
   uniqueness of selections and agreement along declared parent paths.
2. **Generation.** From the resulting signature, derive the types of the
   new record or class, its projections, the parent maps and relative
   maps. Prove that applying a generated projection to its constructor
   reduces to the selected component. The typing of these generated
   bodies belongs in the conclusion. Rechecking them in Rocq provides
   evidence for individual outputs. A general proof would show why every
   signature satisfying formation produces such outputs.
3. **Registration.** Having a well-typed map makes it a candidate for
   registration. Eligibility is a Minks judgment, while acceptance depends
   on Rocq's registration mechanisms and the ambient environment. A
   statement about successful registrations needs explicit assumptions
   about that environment. Predictability of later instance or Canonical
   searches is a further property.

This boundary leaves relative decomposition and Fix-Compose available
as fieldwise substitution theorems, independently of automatic search.

## Research directions and export registration

A direct translation of checked Minks declarations into Rocq dependent
records is one candidate semantics for #50. It should account for which
key each projection selects, including distinct fields of the same type.
The CwF interpretation in #51 asks how closed sublayouts and relative
interfaces behave under substitution. The choice of proof method is open.
[Language specification issue](https://github.com/Godalin/rocq-cats/issues/50) ·
[Categorical interpretation issue](https://github.com/Godalin/rocq-cats/issues/51)

Each export registers its Rocq class and a single Elpi layout with the
packed base, fixed and remaining components, constructor and origin
projections. Mixin inheritance, struct assembly and inspection read the
same layout by its Rocq class reference, including after module functor
application. Extraction is an
instance when a fixed field or declared ancestor view identifies the source.
Remaining mixin fields supply instances for the default keys of the packed
layout. Reverse packers are explicit. No export-to-export views are generated;
the proposed Trans command remains unimplemented.

In a local probe, registering assembly of IsGroup from HasInverse alongside
the generated inverse projection made search revisit the original goal when
no inverse was available. The same cycle occurred without a canonical packer.

## Module scope

Ordinary mixin headers, packed layouts and relative interfaces are regular
Elpi database clauses indexed by Rocq references. The native module system
substitutes those references on functor application. A qualified lookup
opens the defining module in a restored Rocq snapshot and returns only the
requested Elpi data. Opened key names are regular Elpi clauses as well.
Kernel conversion and Section discharge checks for contextual key descriptors
remain in the OCaml plugin. [Modules.v](../examples/Modules.v) checks a
qualified diamond before import and after re-export.
