# Dual constructions and their ordinary interfaces

Concrete setoid models now instantiate the complete constructor layer,
including coproducts, coequalizers, pushouts and indexed/diagram colimits.
See [SetModels](SetModels.md) for explicit choices and model universe bounds.

## One underlying construction

A dual construction uses the original theory on opposite categories. Ordinary
names, notation and arrow directions form an interface to that construction;
there is no independently rebuilt dual object and subsequent comparison theorem.
This rule is recorded in [AGENTS.md](../../AGENTS.md).

## Cocones

[Diagram.Dual](../../theories/Cat/Diagram/Dual.v) stores a cocone `D ⇒∇ X`
through one field, `op_cone : Cone (D^opF) X`. `CoconeN` reads its legs
as the ordinary natural transformation `D ⇒ ConstF J X` and is a coercion,
so components and pointwise equality still use the ordinary interface.
`CoconeOfN` supplies ordinary natural-transformation data to this representation.
Neither adapter introduces a second cocone structure or universal property.

Postcomposition `f ∘Cocone κ` is opposite-cone precomposition. The action
`κ ∘∇ α` of a diagram transformation uses its opposite transformation and
the original vertical composition. `MapCocone F κ` uses `MapCone (F^opF)`
and the existing composition comparison. Laws reuse their original counterparts.
`CoconeCat D` and `CoconeApexF` likewise come from the cone category and apex
functor by opposition. A cocone is represented there by `(X; op_cone κ)`.

## Colimits

[Colimit.Core](../../theories/Cat/Colimit/Core.v) defines
`is_colimit κ := is_limit (op_cone κ)`. `HasColimit C D` contains only
`hasOpLimit : HasLimit (C^op) (D^opF)`. Object `colim D`, injections
`ιcolim[D]`, mediator `colim⟨κ⟩` and their universal laws read the original
limit data and theorems; the data are not reconstructed in a parallel record.

`HasColimitsOfShape C J` contains only the original selected structure
`HasLimitsOfShape (C^op) (J^op)`. `ColimF` is constructed by taking the
opposite of `LimF ∘F OpFctCatF` and adapting the double-opposite endpoints.
Its identity, composition and respectfulness are inherited functor laws.
Importing the modules does not choose any model structures.

## Adjunction and preservation interfaces

[Colimit.Adjunction](../../theories/Cat/Colimit/Adjunction.v) exposes
`ColimF ⊣ Δ[J,C]`. Its two hom maps are the inverse and forward maps of
the original opposite-limit adjunction, read at the ordinary endpoints.
The inverse and naturality laws use the original adjunction laws. Conversely,
`adj_unit_universal` supplies the stored opposite limit directly.
It is not necessary to prove a separate colimit mediator uniqueness theorem.

For arbitrary opposite-shape diagrams, `UnopF` reads a functor between
opposite categories in the original categories. `OpUnopF` supplies the
identity-component comparison back to the original diagram.
[TransportedLimit](../../theories/Cat/Limit/Transport.v) reuses the existing
limit-transport theorem to expose the selected structure at that endpoint.
These are general functor/limit adapters, rather than duplicate dual constructions.

[Colimit.Preservation](../../theories/Cat/Colimit/Preservation.v) directly
uses `right_adjoint_preserves_limit` with `OpAdj` on the stored cone,
then the composition comparison already used by `MapCocone`. The input
assumption is only that the specified source cocone is colimiting.

## Named constructions and their shapes

[Terminal](../../theories/Cat/Terminal.v),
[Coproduct](../../theories/Cat/Coproduct/Core.v) and
[Coequalizer](../../theories/Cat/Coequalizer.v) expose `HasInitial`,
`HasCoproduct` and `HasCoequalizer`. Each contains just the selected terminal,
product or equalizer structure on `C^op`. Their candidate `is_*` properties
are the original properties on `C^op`. Ordinary maps `¡`, `ι1`, `ι2`,
`⦗f,g⦘`, `πcoeq[f,g]` and `coeq⟨q,H⟩` read the original maps directly.
Objects are written `0`, `X ⊔ Y` and `Coeq[f,g]`.

[Terminal](../../theories/Cat/Terminal.v)、

Mediator uniqueness, β/η, respectfulness and composition laws reuse the
original laws. In particular, coequalizer respectfulness compares arrows
without comparing their commutativity witnesses. Initial-object model
construction now supplies its original opposite-terminal data through the
named field `hasOpTerminal`; importing it still makes no model choice.

| Construction | Colimit shape | Characterization |
| --- | --- | --- |
| Initial | `EmptyShape^op` | [`initial_iff_empty_colimit`](../../theories/Cat/Colimit/Initial.v) |
| Binary coproduct | `PairShape^op` | [`coproduct_iff_colimit`](../../theories/Cat/Colimit/Coproduct.v) |
| Coequalizer | `ParallelShape^op` | [`coequalizer_iff_colimit`](../../theories/Cat/Colimit/Coequalizer.v) |
| Pushout | `SpanShape` | [`pushout_iff_colimit`](../../theories/Cat/Colimit/Pushout.v) |

The opposite of a discrete pair is still discrete. In the opposite parallel
shape, the arrows run from `true` to `false`, so the coequalizer projection
is the cocone's `false` component. [Diagram.DualShape](../../theories/Cat/Diagram/DualShape.v)
offers `EmptyCodiagram`, `⟨X,Y⟩CoD`, `⟨f ⇉ g⟩CoD` and the corresponding
`EmptyCocone`, `PairCocone`, `ParallelCocone`, obtained from the original
diagrams and cones through the shared `DualDiagram`/`DualCone` adapters.

[Colimit.Shape](../../theories/Cat/Colimit/Shape.v) restricts the stored
double-opposite cone along `ToDoubleOpF`. This functor is full and essentially
surjective with identity preimages and representative isomorphisms. The
existing limit reindexing theorem then permits direct use of the original
terminal/product/equalizer limit characterizations. Selected structures
convert in both directions through the same reindexing theory; there is no
claim that round-trip selected records are equal. Left-adjoint preservation
likewise applies original right-adjoint preservation to `OpAdj`.

## Pushouts and finite-colimit bases

[Pushout](../../theories/Cat/Pushout.v) stores only
`hasOpPullback : HasPullback (C^op)`. The ordinary object `X ⊔[f,g] Y`,
injections `ιpo1[f,g]`, `ιpo2[f,g]` and mediator `po⟨i,j,H⟩` are the original
opposite pullback data. Its universal property, β/η, respectfulness, witness
independence, uniqueness and square pasting reuse the original theorems.
Pullback uniqueness is transparent so that its inherited isomorphism arrows
remain computational.

[Colimit.Pushout](../../theories/Cat/Colimit/Pushout.v) characterizes arbitrary
span cocones, converts chosen pushouts and span colimits in both directions,
and exposes left-adjoint preservation. `SpanShape` is `CospanShape^op`;
`SpanCocone i j H` uses the shared `DualCone` adapter. These constructions
reuse the same shape-reindexing bridge as the other named colimits.

[Colimit.Finite](../../theories/Cat/Colimit/Finite.v) reads the original
finite-limit constructions in the opposite category:

- Coproducts and coequalizers give pushouts (`CoproductCoequalizerPushout`).
- Initial objects and pushouts give coproducts (`PushoutCoproduct`).
- Coproducts and pushouts give coequalizers (`CoproductPushoutCoequalizer`),
  hence initial objects and pushouts suffice (`PushoutCoequalizer`).

`finite_colimit_bases` converts these two bases in both directions, retaining
the supplied initial structure. It asserts neither equality of selected
records after round trips nor finite colimits from finite limits of `C`.
All selected structures remain opt-in.

## Indexed coproducts and general colimit constructors

[Coproduct.Indexed](../../theories/Cat/Coproduct/Indexed.v) uses the existing
`HasColimit C (DiscreteF D)` as its chosen structure. Write `∐[D]` for the
object, `ι∐[D] i` for an injection and `∐⟨κ⟩` for copairing. The β/η,
respectfulness, composition and arrow-extensionality laws reuse colimit laws.
`IndexedCoproductOpProduct` reads a single coproduct as an opposite indexed
product, retaining its apex definitionally. Discrete self-duality and the
identity-component comparison of discrete diagrams only adapt its diagram.

[Coproduct.Finite](../../theories/Cat/Coproduct/Finite.v) exposes the original
recursive opposite finite product, including its injections and copairing;
the empty family uses the selected initial object.
[Coproduct.Sigma](../../theories/Cat/Coproduct/Sigma.v) reads the original nested
sigma-product construction as a coproduct over a dependent sum of indices.
[Coproduct.Transport](../../theories/Cat/Coproduct/Transport.v) inherits change
of injections, isomorphisms of summands and detection of arrow equality from
the original product transport theory. The foundational module is now
[Coproduct.Core](../../theories/Cat/Coproduct/Core.v).

[Colimit.Construction](../../theories/Cat/Colimit/Construction.v) requires only
two particular coproducts for an individual diagram, plus coequalizers:
the coproduct over its objects and the coproduct over the sources of its
arrows. For an arrow `f : i → j`, the two maps send its source summand by
the injection at `i` or by `D(f)` followed by the injection at `j`.
Their coequalizer is the original product/equalizer limit in the opposite
category. Ordinary constraint maps, candidate cocones and their colimit
property are wrappers of the original constraint maps, cones and theorem.
The uniform version asks for choices over those two discrete index types.

Internally, source summands are indexed by `ArrowOb (J^op)`; its `arrow_cod`
is the source in `J`. This reverses dependent endpoint data directly, without
an equality of arrow records or an additional quotient. Likewise,
[Colimit.Graph.Core](../../theories/Cat/Colimit/Graph/Core.v) indexes coproducts
only by vertices and reversed generators, using `OpFreeF` to transfer the
original graph limit to the opposite free shape.

## Finite shapes, transport and reindexing

[Graph.Opposite](../../theories/Graph/Opposite.v) defines `G^opG`, path reversal
`p^opP` and reading back `p^unopP`, with respectful round trips by specified
path equality. [Free](../../theories/Cat/Free.v) supplies the full, essentially
surjective comparison of `FreeCat (G^opG)` and `(FreeCat G)^op`, in both
directions. No equality of graph or category records is required.

[Shape.Finite](../../theories/Cat/Shape/Finite.v) reverses finite hom covers
and finite generating graphs through `OpFiniteHomCover` and
`OpFiniteGen`. [Colimit.Finite](../../theories/Cat/Colimit/Finite.v)
then wraps the original opposite `FiniteLimits` and `GeneratedLimits`.
Both initial+coproducts+coequalizers and initial+pushouts supply colimits
for finite **and finitely generated** shapes.
[Colimit.Graph.Finite](../../theories/Cat/Colimit/Graph/Finite.v) supplies the
finite-free-graph interface and coproducts over its total generator index.
Cycles and additional path equations remain allowed; finite generation
does not assert a finite hom cover or a finite presentation.

[Colimit.Transport](../../theories/Cat/Colimit/Transport.v) uses original limit
transport for equal cocones and invertible diagram transformations.
[Colimit.Reindex](../../theories/Cat/Colimit/Reindex.v) transfers colimits along
full, essentially surjective shape functors, with selected structures in both
directions. Detection alone requires essential surjectivity.
[Diagram.Reindex](../../theories/Cat/Diagram/Reindex.v) exposes `κ ∘∇F Q` and
`ExtendCocone`, respectfulness and pointwise round trips through the original
opposite cone operations. Composition comparisons use natural isomorphisms,
not equality of functor records.

## Validation and scope

Equalities use the designated setoid relations. Witnesses remain Type-valued
and computational maps transparent. The existing five permanent checks in
[Universes](../../tests/Universes.v) cover independent hom/equality levels,
larger shapes and mixed-category preservation. Four additional permanent
checks cover the named structure/shape conversions in both directions and
both hom/equality orderings, now including pushouts. Two checks cover the
finite-colimit basis conversions in the same orderings. Concrete computations
and assumption audits remain temporary.

The named initial/coproduct/coequalizer modules have been checked locally
with Rocq 9.0.1, OCaml 5.3.0 and Nix Dune 3.23.1. Full build, test and install
targets pass. Twenty-seven temporary assumption checks have no additional
assumptions. Temporary computations use distinct representatives and
extra Type-valued equality witnesses, including a parallel pair with
different raw outputs coequalized by specified setoid equality; its cocone
and colimit mediator reduce directly. Direct backend identity checks also
confirm that copairing and coequalizer factors are the original maps.

The pushout and finite-basis additions pass the same full local build, test
and install targets. Twenty-four temporary assumption checks have no additional
assumptions. Temporary computations check pushout mediators with distinct
setoid representatives and extra Type-valued equality witnesses, plus direct
identity with the original pullback mediator. The selected span-colimit
mediator also reduces to the expected coordinates through the shared shape
adapter.

The completed constructor layer passes the same full local build, test and
install targets. Eight additional permanent universe checks cover both size
orderings for finite/generated, general-diagram, graph-generated and reindexed
colimits. Seventy-six temporary assumption checks have no additional assumptions.
Temporary computations include finite/indexed copairing, general and graph
colimit mediators, a cyclic generating graph whose edge changes raw setoid
representatives, path reversal, and preservation of a selected indexed apex.
Dependent-index coproducts, transported colimits and reindexed colimits also
reduce to the expected injection/mediator composites.

This completes the named, indexed, finite/generated and product/equalizer-based
duality milestone in issue #22. It does not assert that finite limits of a
category give its finite colimits. General Kan extensions and unrelated
categorical structures require separately scoped developments.
