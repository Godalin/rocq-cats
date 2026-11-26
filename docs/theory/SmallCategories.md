# Small categories and diagram shapes

Import the shape catalog for indexing categories and the diagram catalog
for their interpretations. Each shape can index a diagram in any target
category; existence of its limits is a separate hypothesis.
[Shape catalog](../../theories/Cat/Shape/Core.v) · [Diagram catalog](../../theories/Cat/Diagram/Shape.v)

| Shape | Generating data | Typical diagram |
| --- | --- | --- |
| `EmptyShape`, `PointShape` | Zero or one object | Empty diagram or chosen object |
| `DiscreteCat V`, `PairShape` | Vertices only | Indexed family or pair |
| `ArrowShape` | One nonidentity arrow | A single map |
| `SpanShape`, `CospanShape` | Two arrows out of or into a common vertex | Pushout or pullback shape |
| `ParallelShape` | Two parallel arrows | Equalizer shape |
| `SquareShape` | Four edges and a commuting square | Equality of the two diagonal composites |
| `IsoShape` | Two inverse arrows | Chosen isomorphism |
| `[Ord n]` | Ordered positions from 0 through n | A composable chain |
| `CodiscreteCat V` | A unique arrow between any two vertices | Codiscrete groupoid |

Discrete and freely generated diagrams use graph interpretations. A square
also imposes a relation. Its commutativity proof supplies the naturality of
`ArrowN`; uncurrying this transformation gives the square diagram. Each edge
has a hom equation. Parallel cones similarly expose the one equation needed
to construct equalizers. [Arrow diagrams](../../theories/Cat/Diagram/Arrow.v) · [Square diagrams](../../theories/Cat/Diagram/Square.v) · [Uncurrying](../../theories/Cat/Functor/Uncurry.v)

Finite positions use `Fin n`; the natural-number order category has a
computational, type-valued order. Tests exercise diagram constructions
with distinct universes for hom carriers and their equality witnesses.
[Finite sets](../../theories/Set/Finite.v) · [Natural-number order](../../theories/Instance/Nat/Order.v) · [Universe checks](../../tests/Universes.v)
