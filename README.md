# ~~Rocq Abstract Nonsense~~ :)
# Rocq-Cats

A category theory library for self study.

## Key Features

### Category Theory

- Fully Axiom Free / Constructive.

- Modularity with sub-/super- type classes [see here](/theories/Cat/Core.v).

- `CCC` and `ETCS` theories ([see here](/theories/Cat/CCC.v) and [here](/theories/Cat/CCC.v)) can be build up from this modularity.

- A Fully formalized category of sets `SetCat` [see here](./theories/Instance/Set/Core.v)
  - with the following the Rocq features
    - setoid as sets
    - proper function preserving equivalence relations
    - canonical structure
  
- The Yoneda lemma is proved as a setoid isomorphism, with naturality equations
  in the representing object and the set-valued functor
  [see here](./theories/Instance/Set/Yoneda.v).

- Explicit setoid models cover binary/indexed products and coproducts,
  equalizers/coequalizers, pullbacks/pushouts and finite, finitely generated,
  graph-generated and size-bounded general diagram limits/colimits.
  See [the models and their universe bounds](./docs/SetModels.md).

- [CCC structural theory](./docs/CCCStructure.md) provides canonical exponential
  isomorphisms and their naturality, limit preservation, cartesian closed functor
  composition, internal hom equations and native hom-setoid correspondences.

- [Groupoids](./theories/Cat/Groupoid/Core.v) extend existing categories by
  invertibility of every arrow. Inverse coherence is derived from uniqueness;
  [functor and equivalence laws](./theories/Cat/Groupoid/Functor.v) and the
  [thin equality groupoid of a setoid](./theories/Instance/Set/Groupoid.v)
  retain specified equality and independent carrier/witness universes.
  [Setoid groups](./theories/Algebra/Group/Core.v) give
  [single-object groupoids](./theories/Algebra/Group/Category.v).
  The [boolean xor group and its action](./theories/Instance/Bool/Action.v)
  provide a non-thin example whose nonidentity loop swaps boolean elements;
  its regular action reuses the covariant Hom functor.
  [Coherent families are equivalent to equality-groupoid actions](./theories/Instance/Set/Fam/Groupoid.v),
  with reindexing corresponding to precomposition. Composing this comparison
  with Family-Slice gives an
  [equivalence between actions and slices](./theories/Instance/Set/Fam/GroupoidSlice.v)
  under the existing Family-Slice size bound.

- The [simplex category](./theories/Cat/Shape/Simplex/Core.v) reuses finite
  ordinal categories and the induced-category construction. Natural-isomorphism
  equality of its arrows is equivalent to pointwise equality of positions.
  [Cofaces and codegeneracies](./theories/Cat/Shape/Simplex/Operators.v) use
  bounded finite indices and satisfy the simplicial identities.
  [Simplicial setoids](./theories/Instance/Set/Simplicial/Core.v) reuse the
  presheaf category; their
  [faces and degeneracies](./theories/Instance/Set/Simplicial/Operators.v)
  inherit these identities by restriction.
  [Standard simplices](./theories/Instance/Set/Simplicial/Standard.v) form a
  fully faithful Yoneda embedding, with maps from the standard n-simplex
  corresponding naturally to n-simplices. Explicit universe lifts keep small
  simplex operators compatible with larger setoid values.
  The [diagram nerve](./theories/Instance/Set/Simplicial/Nerve.v), written
  `N≅(C)`, specializes a general
  [category-probe presheaf](./theories/Instance/Set/Functor.v).
  Its simplices are finite-ordinal diagrams compared by natural isomorphism;
  the nerve of a finite ordinal is naturally isomorphic to its standard simplex.
  The proved groupoid boundary is significant: two n-simplices are equal
  exactly when their first vertices are isomorphic. Thus all same-degree
  simplices of a one-object groupoid are equal in this construction.
  The [monoid arrow-chain nerve](./theories/Instance/Set/Simplicial/Monoid.v)
  now supplies this distinction for single-object categories: its n-simplices
  are n-tuples with pointwise setoid equality, and restriction composes
  consecutive arrow segments. The reusable
  [segment subdivision theory](./theories/Algebra/Monoid/Chain.v) proves its
  functor laws. Its [boolean model](./theories/Instance/Bool/Nerve.v) has
  distinct identity and nontrivial loops, and proves that their images in the
  diagram nerve become equal.
  The [vertex nerve](./theories/Instance/Set/Simplicial/Vertex.v), `Nᵥ(T)`,
  extends this distinction to categories equipped with an object setoid and
  a coherent object action `T : EqGpd(X) → C`. Its
  [labelled diagrams](./theories/Instance/Set/VertexDiagram.v) compare vertices
  by the specified setoid equality and arrows by squares with the prescribed
  transports. Consecutive arrows suffice to check simplex equality.
  The [singleton comparison](./theories/Instance/Set/Simplicial/MonoidVertex.v)
  is a natural isomorphism with the original monoid nerve; forgetting vertex
  comparisons recovers the earlier map to the diagram nerve. A bare category
  does not itself select this extra object equality and transport data.
  Full-faithfulness, coskeletality and Kan theory remain open.
  The [spine correspondence](./theories/Instance/Set/Simplicial/Spine.v)
  identifies every degree of the vertex nerve with the
  [setoid of composable chains](./theories/Instance/Set/VertexChain.v).
  Both reconstruction and its uniqueness follow from the
  [general finite-chain interpretation](./theories/Cat/Chain.v);
  simplex restriction corresponds to composing the image intervals of a chain.
  [Local two-dimensional horns](./theories/Instance/Set/Simplicial/Horn2.v)
  fix three vertices and retain two triangle edges. Inner horns have unique
  fillers in every category; both outer restrictions are isomorphisms in a
  groupoid, and the resulting realized two-simplices are unique under the
  specified equality. Conversely, chosen outer fillers characterize groupoids
  through the [general division criterion](./theories/Cat/Groupoid/Division.v).
  [Boundaries and horns](./theories/Instance/Set/Simplicial/Boundary.v)
  are actual subpresheaves of standard simplices, constructed uniformly from
  [generated sieves](./theories/Cat/Sieve.v). Their inclusions are monic;
  membership retains a face factorization, while equality compares only the
  underlying simplex operator. The [general sieve theory](./theories/Instance/Set/Sieve.v)
  proves generator extensionality and the Yoneda extension correspondence.
  [Horn maps and fillers](./theories/Instance/Set/Simplicial/Horn.v) use these
  interfaces; local retained-edge equality already implies equality of the
  entire realized horn map. Recovering local data from arbitrary horn maps
  and the full Kan criterion remain to be proved.

### ETCS

This project aims at building ETCS.

## Building

Requires Rocq / Stdlib 9.0 or later and Dune 3.23 or later. The project uses
the Rocq build language; [Dune 3.23](https://github.com/ocaml/dune/releases/tag/3.23.0)
fixes configuration discovery for Rocq 9.0.
With these tools available, run `dune build @all @runtest @install`.

For the local `rocq-env` opam switch, [shell.nix](./shell.nix) supplies a pinned
Dune 3.23.1 independently of the switch's packages:

```sh
opam exec --switch=rocq-env -- nix-shell --run 'dune build @all @runtest @install'
```

The shell inherits Rocq and OCaml from the caller; it does not install a
Rocq toolchain. The local VS Code build task uses this same environment.

## Repository layout

- [Algebra](./theories/Algebra/): setoid monoids and groups, their single-object
  categorical interpretations, endomorphism structures, and regular actions.
  The algebraic core modules depend on foundational sets, not categories.
- [Set](./theories/Set/): foundational sets with designated Type-valued equality.
  [Core](./theories/Set/Core.v) defines `SetC`;
  [Morphism](./theories/Set/Morphism.v) defines respectful maps and function sets.
  This layer does not depend on categories; see the
  [foundation and migration note](./docs/FoundationalSets.md).
- [Cat](./theories/Cat/): categorical interfaces and general constructions.
  Topic extensions are grouped under [Arrow/](./theories/Cat/Arrow/),
  [Slice/](./theories/Cat/Slice/) and [Bicategory/](./theories/Cat/Bicategory/),
  alongside their core modules. [Shape/](./theories/Cat/Shape/) contains index
  categories; [Diagram.Shape](./theories/Cat/Diagram/Shape.v) collects diagram
  constructors grouped by mathematical subject.
  [Core](./theories/Cat/Core.v) contains categories, duality, product categories,
  and isomorphisms. Each hom is a `HomSet : SetC`; `Hom` and `HomEq` are derived.
  Universal constructions are provided separately by
  [Terminal](./theories/Cat/Terminal.v) (including initial objects),
  [Product](./theories/Cat/Product/Core.v),
  [Exponential](./theories/Cat/Exponential/Core.v), and
  [Pullback](./theories/Cat/Pullback.v).
  [Slice](./theories/Cat/Slice/Core.v) constructs `C /C X`, with commuting triangles
  up to morphism equivalence and equality on their underlying arrows.
  [Arrow](./theories/Cat/Arrow/Core.v) constructs `Arr C`, with commuting squares,
  domain/codomain functors, and the functor induced by a natural transformation.
  [Section](./theories/Cat/Section.v) defines `Sec(p)` for any category,
  retaining right-inverse witnesses and comparing the section maps. It maps
  sections along commuting maps over a base (`f ▷Sec[H] s`) and pulls them
  back along a given universal square (`s[HP]Sec`).
  [Slice.Reindex](./theories/Cat/Slice/Reindex.v) gives pullback functors on slices,
  with specified natural identity and composition comparisons; write `A[f]C`.
  [Slice.Arrow](./theories/Cat/Slice/Arrow.v) embeds slice maps as squares over the
  identity. Write `A^Arr` for the arrow object. Slice reindexing, including its
  unit/composition comparisons, agrees with codomain cartesian factorization
  for the same chosen pullbacks; `SliceReindexSquareN f` packages the natural squares.
  [Functor](./theories/Cat/Functor/Core.v) and
  [Natural](./theories/Cat/Natural.v) extend opposition to functors (`F ^opF`)
  and natural transformations (`α ^opN`). Functors are compared by natural
  isomorphism (`F ≅N G`), without requiring equality of their object values.
  Whiskering is written `G ∘Nl α` and `β ∘Nr F`; composition, fixing arguments,
  and taking opposites preserve natural isomorphisms.
  [Diagram.Dual](./theories/Cat/Diagram/Dual.v) provides cocones `D ⇒∇ X`
  and their correspondence with opposite cones.
  [Colimit](./theories/Cat/Colimit/Core.v) reuses opposite limits, with
  [diagonal adjunctions](./theories/Cat/Colimit/Adjunction.v) and
  [left-adjoint preservation](./theories/Cat/Colimit/Preservation.v);
  [initial objects](./theories/Cat/Colimit/Initial.v),
  [coproducts](./theories/Cat/Colimit/Coproduct.v),
  [coequalizers](./theories/Cat/Colimit/Coequalizer.v) and
  [pushouts](./theories/Cat/Colimit/Pushout.v) have corresponding
  colimit characterizations and explicit conversions of chosen structures.
  Write `X ⊔ Y`, `⦗f,g⦘`, `Coeq[f,g]` and `πcoeq[f,g]` for the ordinary
  interfaces to opposite products and equalizers. Pushouts use
  `X ⊔[f,g] Y`, `ιpo1[f,g]`, `ιpo2[f,g]` and `po⟨i,j,H⟩`.
  The [finite-colimit bases](./theories/Cat/Colimit/Finite.v) convert between
  initial objects with pushouts and initial objects with coproducts and
  coequalizers, and construct colimits of finite or finitely generated shapes.
  [Indexed coproducts](./theories/Cat/Coproduct/Indexed.v) use `∐[D]`,
  `ι∐[D]` and `∐⟨κ⟩`, with
  [finite](./theories/Cat/Coproduct/Finite.v) and
  [dependent-index](./theories/Cat/Coproduct/Sigma.v) constructions.
  [General diagram colimits](./theories/Cat/Colimit/Construction.v) and
  [generator-based colimits](./theories/Cat/Colimit/Graph/Core.v) reuse the
  opposite product/equalizer theory. Colimits also support
  [transport](./theories/Cat/Colimit/Transport.v) and
  [shape reindexing](./theories/Cat/Colimit/Reindex.v);
  see the [duality guide](./docs/Duality.md).
  [CatCat](./theories/Cat/CatCat.v) provides the category of categories with
  this morphism equivalence. Write `C ≃C D` for an equivalence with chosen
  quasi-inverse functors and natural isomorphisms for the two composites.
  The double-opposite comparison is a natural isomorphism whose component
  functors act as identities on objects and morphisms.
  [Bicategory](./theories/Cat/Bicategory/Core.v) introduces hom-categories, horizontal
  composition, interchange, and coherent associators/unitors.
  [Bicategory.Strict](./theories/Cat/Bicategory/Strict.v) expresses strictness relative to
  a specified 1-cell equivalence (`f ≈₁[R] g`), with coherent comparison
  2-cells and strict associators/unitors. Write `α⟦p, q⟧₂` for transport of
  both endpoints of a 2-cell along specified 1-cell equivalences.
  [Bicategory.Thin](./theories/Cat/Bicategory/Thin.v) gives a locally thin strict model
  from any category, retaining its morphism-equivalence witnesses as 2-cells.
  [Bicategory.Cat](./theories/Cat/Bicategory/Cat.v) retains all natural
  transformations as 2-cells and proves pentagon/triangle coherence. `CatCat`
  remains its separate one-dimensional shadow up to natural isomorphism.
  [Bicategory.Homotopy](./theories/Cat/Bicategory/Homotopy.v) constructs this shadow for any
  bicategory; the shadow of `CatBicat` is explicitly equivalent to `CatCat`.
  [The design note](./docs/TwoCategories.md) explains the levels of equality
  in this bicategory presentation. The small
  [natural-number model](./theories/Instance/Nat/TwoCat.v) has
  noninvertible 2-cells and satisfies this setoid strictness interface.
  [Fibration](./theories/Cat/Fibration.v) defines cartesian morphisms by universal
  factorization, compares lifts over a base isomorphism, and provides chosen
  cartesian lifts with explicit base-object identifications.
  [Arrow.Fibration](./theories/Cat/Arrow/Fibration.v) proves that cartesian arrows
  of the codomain functor are precisely pullback squares. Chosen pullbacks and
  chosen codomain lifts yield one another by explicit constructions; write
  `B[σ]Arr` for the pullback arrow object. Both choices require explicit activation.
  [Comprehension](./theories/Cat/Comprehension.v) combines chosen lifts with a
  total-space functor and a natural projection, requiring cartesian morphisms
  to give pullback squares. Write `A ^ext[K]` for the extension and `π[K] A`
  for its display projection. `ComprehensionF K` is its functor to the arrow category;
  fullness and faithfulness are separate properties.
- [Instance/Set](./theories/Instance/Set/): concrete implementations using setoids
  as sets. [Core](./theories/Instance/Set/Core.v) defines their category `SetCat`;
  [Product](./theories/Instance/Set/Product.v),
  [Pullback](./theories/Instance/Set/Pullback.v), and
  [Fam](./theories/Instance/Set/Fam/Core.v) provide independent extensions.
  [FamCat](./theories/Instance/Set/Fam/Cat.v) assembles coherent families and
  transport-compatible maps into a category, with base and total-space
  functors to `SetCat` and their natural projection.
  [FamFixed](./theories/Instance/Set/Fam/Fixed.v) gives the category `FamSCat X`
  of families over a fixed base and fiberwise maps `A →Fam B`.
  [FamSlice](./theories/Instance/Set/Fam/Slice.v) constructs total-space and
  fiber functors and proves `FamSCat X ≃C (SetCat /C X)`; see the
  [families–slices note](./docs/FamiliesAndSlices.md) for the size bounds and
  compatibility with substitution.
  [FamSliceReindex](./theories/Instance/Set/Fam/SliceReindex.v) proves that taking
  total spaces commutes with reindexing up to a specified natural isomorphism,
  compatible with the identity and composition comparisons on both sides.
  It also compares fiber formation with reindexing, compatibly with the sum
  comparison and the two round-trip natural isomorphisms.
  [FamReindex](./theories/Instance/Set/Fam/Reindex.v) gives canonical reindexing
  morphisms whose total-space squares satisfy the pullback universal property.
  Identity and composition of reindexing are compared by explicit family
  isomorphisms that act as identities on the base and fibers.
  Write `A[f]S` for reindexing a coherent family and `U[f]` for reindexing a
  family object, including its base; successive reindexing is `U[f][g]`.
  [FamFibration](./theories/Instance/Set/Fam/Fibration.v) proves reindexing
  cartesian for `FamBaseF`. Its chosen structure `FamBaseF_HasCartesianLift`
  is enabled explicitly; the abstract lift `f ^*[FamBaseF] U` then computes to
  `U[f]`. The reindexed family morphism `φ⟦f⟧` acts directly on fibers.
  [FamSection](./theories/Instance/Set/Fam/Section.v) provides coherent sections,
  their reindexing, the generic element, and total-space pairing with its
  universal property and β/η laws; `s ≈s t` compares sections pointwise.
  Coherent sections are isomorphic to `Sec(p)`, the setoid of right inverses
  of the total-space projection `p`, whose equality compares the maps.
  [FamSectionMap](./theories/Instance/Set/Fam/SectionMap.v) connects sections to
  family morphisms: `φ ▷ s` acts on a section, while `φ ▷[f] s` acts on a section
  already reindexed along `f`. Equivalent morphisms give equivalent values
  after transport along their base-map equivalence. The action over `f` agrees
  with the action of `φ⟦f⟧`, using the identity comparison on sections.
  [FamComprehension](./theories/Instance/Set/Fam/Comprehension.v) assembles these
  constructions into a comprehension structure and proves the total-space
  pullback property for every cartesian family morphism.
  [Hom](./theories/Instance/Set/Hom.v), [Yoneda](./theories/Instance/Set/Yoneda.v),
  [Presheaf](./theories/Instance/Set/Presheaf.v), and
  [Subobject](./theories/Instance/Set/Subobject.v) contain the set-valued
  constructions.
  [Representable](./theories/Instance/Set/Representable.v) relates covariant and
  contravariant representations to universal elements over any category,
  with transparent mediators and unique comparisons preserving the generic element.
  Write `X ⦂ Rep F`, `X ⦂ Repᵒᵖ P` and `u ⦂ Univ(F)` for these structures;
  cartesian morphisms use the same annotation style, `f ⦂ Cart(P)`.
  [Terminal](./theories/Instance/Set/Terminal.v) and
  [Initial](./theories/Instance/Set/Initial.v) provide the unit and empty objects.
  [Exponential](./theories/Instance/Set/Exponential.v) constructs respectful-map
  exponentials; [CCC](./theories/Instance/Set/CCC.v) assembles the cartesian
  closed structure `SetCat_CCC : CCC SetCat` without additional axioms.
  [Nat](./theories/Instance/Set/Nat.v) provides a natural-numbers object with
  computational recursion.
  [CwF](./theories/Instance/Set/CwF.v) constructs `SetCwF El` from a chosen
  coherent decoding family. Types are code-valued maps and terms are coherent
  sections; context extension uses their dependent sum.
- [DTT](./theories/DTT/): dependent type theory interfaces.
  [Display](./theories/DTT/Display/Core.v) specifies coherent display maps over a
  type presheaf, with designated-equality conversion and chosen display pullbacks.
  [Context/Display](./theories/DTT/Context/Display.v) constructs this choice from
  context extensions, without requiring a terminal object or arbitrary pullbacks.
  [Display/Section](./theories/DTT/Display/Section.v) constructs `DisplayTyTmF P`
  in the reverse direction: terms are sections of the display projections,
  conversion is `e ▸D[P] s`, and substitution is `s[σ]TmD[P]`.
  Representing its pair presheaves remains a separate step.
  [CwF](./theories/DTT/CwF.v) organizes types, terms and coherent substitution
  through a family-valued presheaf, with context extensions specified by a
  universal property. [ContextExtension](./theories/DTT/Context/Extension.v)
  derives their representing-set isomorphisms, naturality and pairing
  compatibility with substitution.
  [ContextRepresentation](./theories/DTT/Context/Representation.v) recovers context
  extensions from chosen representations of the pair presheaves, compares both
  round trips, and assembles a CwF when a terminal context is chosen.
  The [recovery design](./docs/CwFRecovery.md) separates this criterion from the
  additional data needed to recover types and coherent terms from comprehension.
  [ContextConversion](./theories/DTT/Context/Conversion.v) derives context-extension
  isomorphisms along designated type equality, preserving projections and
  converted generic terms. [ContextPullback](./theories/DTT/Context/Pullback.v)
  constructs coherent substitution lifts and pullbacks of display projections
  from the extension universal property.
  [Comprehension](./theories/DTT/Comprehension.v) forms the total category of
  types with commuting display squares and constructs its comprehension
  structure; cartesian arrows are precisely the pullback squares, and its
  functor to the arrow category is fully faithful.
  [ContextSection](./theories/DTT/Context/Section.v) identifies terms with sections
  of display projections, compatibly with pairing and substitution.
  Write `t^Sec[T,A]` and `s^Tm[T,A]` for the two directions.
  See the [design note](./docs/CwFDesign.md).
- [ETCS](./theories/ETCS/): abstract ETCS interfaces and results.

Chosen universal constructions share the same design: `is_*` describes a
specific candidate, and `Has*` stores a chosen candidate with that universal
property. Mediating maps are extracted from transparent witnesses; their laws,
uniqueness, and respectfulness follow from the property. This covers
[products](./theories/Cat/Product/Core.v),
[terminal and initial objects](./theories/Cat/Terminal.v),
[exponentials](./theories/Cat/Exponential/Core.v),
[pullbacks](./theories/Cat/Pullback.v),
[natural-numbers objects](./theories/ETCS/Nat.v), and
[subobject classifiers](./theories/ETCS/Sub.v).

Import the setoid structures that are needed and enable chosen structures explicitly:

```coq
From Cats Require Import Instance.Set.Core.
From Cats Require Import Instance.Set.Product Instance.Set.Pullback.

Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasPullback.
```

The complete cartesian closed structure can also be enabled as a bundle:

```coq
From Cats Require Import Instance.Set.CCC.
Local Existing Instance SetCat_CCC.
```

The [CCC/STLC research note](./docs/CCCAndSTLC.md) explains the interpretation
of simple types, contexts, substitution and βη equations in an arbitrary CCC.
The reusable [exponential laws](./theories/Cat/Exponential/Core.v) and
[hom-setoid correspondence](./theories/Instance/Set/ExponentialHom.v) are implemented;
the general [adjunction theory](./theories/Cat/Adjunction.v) starts with natural
hom isomorphisms and derives unit/counit and composition, including `(-) × A ⊣ (-)^A`.
The [limit theory](./docs/Limits.md) derives limit functors, the diagonal
adjunction and preservation of limits by right adjoints from universal properties.
The [graph and free-category constructions](./docs/Graphs.md) generate diagram
shapes and identify binary products and pullbacks with their corresponding limits.
The [small-category catalogue](./docs/SmallCategories.md) also provides arrows,
spans, parallel pairs, commuting squares, walking isomorphisms and finite ordinals.
Empty and parallel-pair limits are identified with terminal objects and
equalizers; all four shape correspondences derive right-adjoint preservation
from the general limit theorem.
The [finite-limit basis constructions](./theories/Cat/Limit/Finite.v) convert
terminal objects and pullbacks to terminal objects, binary products and
equalizers, and conversely, with explicit chosen structures.
The [general limit construction](./theories/Cat/Limit/Construction.v) uses
the equalizer of two maps between object-indexed and arrow-indexed products;
indexed products reuse discrete limits directly.
The [finite product construction](./theories/Cat/Product/Finite.v) derives
limits of finite discrete diagrams from terminal objects and binary products,
using shared [finite positions](./theories/Set/Finite.v).
The [generator-based construction](./theories/Cat/Limit/Graph/Core.v) needs products
only over vertices and generating edges. Its
[finite-graph specialization](./theories/Cat/Limit/Graph/Finite.v) derives limits
from terminal objects, binary products and equalizers, including shapes with cycles.
The [shape-transfer theorem](./theories/Cat/Limit/Reindex.v) transfers limits
along full, essentially surjective functors, using object isomorphisms and
specified hom equality without requiring faithfulness.
The [cone presheaf comparison](./theories/Cat/Diagram/Presheaf.v) packages
restriction and extension as an explicit natural setoid isomorphism in the
apex, with a specialization to chosen finite generators.
[STLC.Free](./theories/STLC/Free.v) provides the completed syntax/semantics result:
interpretation in arbitrary CCCs, semantic substitution, βη soundness and
completeness at a common bound containing the syntax model. Its free-CCC
universal property extends specified base-type isomorphisms to unique natural
transformations, with invertible canonical extensions.
[ContextEquivalence](./theories/STLC/ContextEquivalence.v) identifies the context
and type presentations. See [#9](https://github.com/Godalin/rocq-cats/issues/9)
and [#20](https://github.com/Godalin/rocq-cats/issues/20) for acceptance records.

## TODOs

- [x] Coherent families: base and total-space functors, with the
  projection as a natural transformation (see
  [FamCat](./theories/Instance/Set/Fam/Cat.v)).
- [x] Family reindexing and its total-space pullback universal property (see
  [FamReindex](./theories/Instance/Set/Fam/Reindex.v)).
- [x] Identity and composition comparisons for family reindexing.
- [x] Coherent sections, their reindexing, and total-space pairing.
- [x] Family morphisms acting on sections, with identity and composition laws.
- [x] Cartesian factorization of family reindexing, chosen lifts, and reindexed
  family morphisms acting on sections.
- [x] Abstract comprehension, its coherent-family model, and the correspondence
  between coherent sections and sections of display projections.
- [x] Abstract CwF interface with designated equality, coherent substitution,
  context extensions, and pairing β/η laws.
- [x] Instantiate CwF using a coherent Code/El family of sets.
- [x] Context-extension representability and its substitution naturality.
- [x] Context-extension isomorphisms induced by designated type equality.
- [x] Coherent substitution lifts and pullbacks of context-extension projections.
- [x] A CwF comprehension structure with display-square morphisms and a cartesian/pullback characterization.
- [x] Pullbacks
- [x] Limits: cones, universal properties, limit functors and diagonal adjunctions
- [x] Adjunctions: unit/counit, natural hom correspondence, and composition
- [ ] Univalence Category
- [ ] Enriched Category
- [ ] ETCS constructions
  - [x] Sub-object
  - [ ] Relations
  - [ ] Numbers
  - [ ] Well Orderings
  - [ ] AC
  - [ ] Cardinal Arithmetics
- [ ] *TBA*
