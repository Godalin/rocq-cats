# Documentation

## Library and theory

Start with the [library guide](theory/LibraryGuide.md). It maps the main modules
and explains where the abstract constructions meet their concrete models.

| Topic | Guides |
| --- | --- |
| Foundations and diagrams | [Sets and equality](theory/FoundationalSets.md), [small categories](theory/SmallCategories.md), [graphs and free categories](theory/Graphs.md) |
| Universal properties | [Limits](theory/Limits.md), [duality](theory/Duality.md), [models in sets](theory/SetModels.md) |
| Structured categories | [CCC equations](theory/CCCStructure.md), [universes](theory/StructureUniverses.md), [two-dimensional structure](theory/TwoCategories.md) |
| Syntax and semantics | [CCC and STLC](theory/CCCAndSTLC.md), [families and slices](theory/FamiliesAndSlices.md), [categories with families](theory/CwFDesign.md), [recovering context extension](theory/CwFRecovery.md) |

## Development standards

- [Mathematical interfaces](development/HierarchyDevelopment.md) covers declaring components with Minks, shared choices, implicit arguments and instance search.
- [Rocq source layout](development/CodeStyle.md) covers declarations, notation, line breaks and proofs. The [abbreviation map](development/Abbreviations.md) records public names.
- [Development checks](development/Testing.md) and [parallel development](development/ParallelDevelopment.md) describe validation and worktree integration.
- [Building the reading editions](development/Documentation.md) gives the commands. [Export requirements](development/ExportRequirements.md) defines the presentation of source coqdoc in those editions.
- [Minks](../minks/README.md) maintains its own [command semantics](../minks/doc/formal-semantics.pdf) and [implementation guide](../minks/doc/implementation/README.md).

## Historical audits

The [interface migration survey](history/BundledInterfaces.md) and
[Monad, Applicative and Arrow audit](history/ComputationAudit.md) retain
source-pinned inventories and validation evidence from earlier revisions.
