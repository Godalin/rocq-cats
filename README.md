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

### ETCS

This project aims at building ETCS.

## Repository layout

- [Set](./theories/Set/): foundational sets with designated Type-valued equality.
  [Core](./theories/Set/Core.v) defines `SetC`;
  [Morphism](./theories/Set/Morphism.v) defines respectful maps and function sets.
  This layer does not depend on categories; see the
  [foundation and migration note](./docs/FoundationalSets.md).
- [Cat](./theories/Cat/): categorical interfaces and general constructions.
  [Core](./theories/Cat/Core.v) contains categories, duality, product categories,
  and isomorphisms. Each hom is a `HomSet : SetC`; `Hom` and `HomEq` are derived.
  Universal constructions are provided separately by
  [Terminal](./theories/Cat/Terminal.v) (including initial objects),
  [Product](./theories/Cat/Product.v),
  [Exponential](./theories/Cat/Exponential.v), and
  [Pullback](./theories/Cat/Pullback.v).
  [Slice](./theories/Cat/Slice.v) constructs `C /C X`, with commuting triangles
  up to morphism equivalence and equality on their underlying arrows.
  [SliceReindex](./theories/Cat/SliceReindex.v) gives pullback functors on slices,
  with specified natural identity and composition comparisons; write `A[f]C`.
  [Functor](./theories/Cat/Functor.v) and
  [Natural](./theories/Cat/Natural.v) extend opposition to functors (`F ^opF`)
  and natural transformations (`α ^opN`). Functors are compared by natural
  isomorphism (`F ≅N G`), without requiring equality of their object values.
  Whiskering is written `G ∘Nl α` and `β ∘Nr F`; composition, fixing arguments,
  and taking opposites preserve natural isomorphisms.
  [CatCat](./theories/Cat/CatCat.v) provides the category of categories with
  this morphism equivalence. Write `C ≃C D` for an equivalence with chosen
  quasi-inverse functors and natural isomorphisms for the two composites.
  The double-opposite comparison is a natural isomorphism whose component
  functors act as identities on objects and morphisms.
  [Bicategory](./theories/Cat/Bicategory.v) introduces hom-categories, horizontal
  composition, interchange, and coherent associators/unitors.
  [TwoCategory](./theories/Cat/TwoCategory.v) expresses strictness relative to
  a specified 1-cell equivalence (`f ≈₁[R] g`), with coherent comparison
  2-cells and strict associators/unitors. Write `α⟦p, q⟧₂` for transport of
  both endpoints of a 2-cell along specified 1-cell equivalences.
  [ThinBicat](./theories/Cat/ThinBicat.v) gives a locally thin strict model
  from any category, retaining its morphism-equivalence witnesses as 2-cells.
  [CatBicat](./theories/Cat/CatBicat.v) retains all natural
  transformations as 2-cells and proves pentagon/triangle coherence. `CatCat`
  remains its separate one-dimensional shadow up to natural isomorphism.
  [BicatHomotopy](./theories/Cat/BicatHomotopy.v) constructs this shadow for any
  bicategory; the shadow of `CatBicat` is explicitly equivalent to `CatCat`.
  [The design note](./docs/TwoCategories.md) explains the levels of equality
  in this bicategory presentation. The small
  [natural-number model](./theories/Instance/Nat/TwoCat.v) has
  noninvertible 2-cells and satisfies this setoid strictness interface.
  [Fibration](./theories/Cat/Fibration.v) defines cartesian morphisms by universal
  factorization, compares lifts over a base isomorphism, and provides chosen
  cartesian lifts with explicit base-object identifications.
  [Comprehension](./theories/Cat/Comprehension.v) combines chosen lifts with a
  total-space functor and a natural projection, requiring cartesian morphisms
  to give pullback squares. Write `A ^ext[K]` for the extension and `π[K] A`
  for its display projection.
- [Instance/Set](./theories/Instance/Set/): concrete implementations using setoids
  as sets. [Core](./theories/Instance/Set/Core.v) defines their category `SetCat`;
  [Product](./theories/Instance/Set/Product.v),
  [Pullback](./theories/Instance/Set/Pullback.v), and
  [Fam](./theories/Instance/Set/Fam.v) provide independent extensions.
  [FamCat](./theories/Instance/Set/FamCat.v) assembles coherent families and
  transport-compatible maps into a category, with base and total-space
  functors to `SetCat` and their natural projection.
  [FamFixed](./theories/Instance/Set/FamFixed.v) gives the category `FamSCat X`
  of families over a fixed base and fiberwise maps `A →Fam B`.
  [FamSlice](./theories/Instance/Set/FamSlice.v) constructs total-space and
  fiber functors and proves `FamSCat X ≃C (SetCat /C X)`; see the
  [families–slices note](./docs/FamiliesAndSlices.md) for the size bounds and
  compatibility with substitution.
  [FamSliceReindex](./theories/Instance/Set/FamSliceReindex.v) proves that taking
  total spaces commutes with reindexing up to a specified natural isomorphism,
  compatible with the identity and composition comparisons on both sides.
  It also compares fiber formation with reindexing, compatibly with the sum
  comparison and the two round-trip natural isomorphisms.
  [FamReindex](./theories/Instance/Set/FamReindex.v) gives canonical reindexing
  morphisms whose total-space squares satisfy the pullback universal property.
  Identity and composition of reindexing are compared by explicit family
  isomorphisms that act as identities on the base and fibers.
  Write `A[f]S` for reindexing a coherent family and `U[f]` for reindexing a
  family object, including its base; successive reindexing is `U[f][g]`.
  [FamFibration](./theories/Instance/Set/FamFibration.v) proves reindexing
  cartesian for `FamBaseF`. Its chosen structure `FamBaseF_HasCartesianLift`
  is enabled explicitly; the abstract lift `f ^*[FamBaseF] U` then computes to
  `U[f]`. The reindexed family morphism `φ⟦f⟧` acts directly on fibers.
  [FamSection](./theories/Instance/Set/FamSection.v) provides coherent sections,
  their reindexing, the generic element, and total-space pairing with its
  universal property and β/η laws; `s ≈s t` compares sections pointwise.
  Coherent sections are isomorphic to `Sec(p)`, the setoid of right inverses
  of the total-space projection `p`, whose equality compares the maps.
  [FamSectionMap](./theories/Instance/Set/FamSectionMap.v) connects sections to
  family morphisms: `φ ▷ s` acts on a section, while `φ ▷[f] s` acts on a section
  already reindexed along `f`. Equivalent morphisms give equivalent values
  after transport along their base-map equivalence. The action over `f` agrees
  with the action of `φ⟦f⟧`, using the identity comparison on sections.
  [FamComprehension](./theories/Instance/Set/FamComprehension.v) assembles these
  constructions into a comprehension structure and proves the total-space
  pullback property for every cartesian family morphism.
  [Hom](./theories/Instance/Set/Hom.v), [Yoneda](./theories/Instance/Set/Yoneda.v),
  [Presheaf](./theories/Instance/Set/Presheaf.v), and
  [Subobject](./theories/Instance/Set/Subobject.v) contain the set-valued
  constructions.
  [Terminal](./theories/Instance/Set/Terminal.v) and
  [Initial](./theories/Instance/Set/Initial.v) provide the unit and empty objects.
  [Exponential](./theories/Instance/Set/Exponential.v) constructs respectful-map
  exponentials; [CCC](./theories/Instance/Set/CCC.v) assembles the cartesian
  closed structure `SetCat_CCC : CCC SetCat` without additional axioms.
  [Nat](./theories/Instance/Set/Nat.v) provides a natural-numbers object with
  computational recursion.
- [DTT](./theories/DTT/): dependent type theory interfaces.
  [CwF](./theories/DTT/CwF.v) organizes types, terms and coherent substitution
  through a family-valued presheaf, with context extensions specified by a
  universal property. See the [design note](./docs/CwFDesign.md).
- [ETCS](./theories/ETCS/): abstract ETCS interfaces and results.

Chosen universal constructions share the same design: `is_*` describes a
specific candidate, and `Has*` stores a chosen candidate with that universal
property. Mediating maps are extracted from transparent witnesses; their laws,
uniqueness, and respectfulness follow from the property. This covers
[products](./theories/Cat/Product.v),
[terminal and initial objects](./theories/Cat/Terminal.v),
[exponentials](./theories/Cat/Exponential.v),
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

## TODOs

- [x] Coherent families: base and total-space functors, with the
  projection as a natural transformation (see
  [FamCat](./theories/Instance/Set/FamCat.v)).
- [x] Family reindexing and its total-space pullback universal property (see
  [FamReindex](./theories/Instance/Set/FamReindex.v)).
- [x] Identity and composition comparisons for family reindexing.
- [x] Coherent sections, their reindexing, and total-space pairing.
- [x] Family morphisms acting on sections, with identity and composition laws.
- [x] Cartesian factorization of family reindexing, chosen lifts, and reindexed
  family morphisms acting on sections.
- [x] Abstract comprehension, its coherent-family model, and the correspondence
  between coherent sections and sections of display projections.
- [x] Abstract CwF interface with designated equality, coherent substitution,
  context extensions, and pairing β/η laws.
- [ ] Instantiate CwF using a coherent Code/El family of sets.
- [x] Pullbacks
- [ ] Limits
- [ ] Adjoint Functor
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
