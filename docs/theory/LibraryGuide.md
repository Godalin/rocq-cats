# Library guide

Start with sets and respectful maps, then categories, functors and natural
transformations. The library has three independent directions beyond that
foundation: cartesian closed categories and typed syntax, toposes and ETCS,
and dependent type theory.

| To study | Start here | Continue with |
| --- | --- | --- |
| Equality and universal properties | [Sets](FoundationalSets.md) and [categories](../../theories/Cat/Core.v) | [Limits](Limits.md) and [concrete models](SetModels.md) |
| Shared algebraic structure | [Magma](../../theories/Algebra/Magma/Core.v) | [Groups](../../theories/Algebra/Group/Core.v) and [symmetric monoidal categories](../../theories/Cat/Monoidal/Symmetric.v) |
| Syntax and interpretation | [Cartesian closed structure](CCCStructure.md) | [The free CCC and STLC](CCCAndSTLC.md) |
| Categorical logic | [Elementary toposes](../../theories/Topos/Core.v) | [ETCS](../../theories/Topos/ETCS.v) |
| Substitution and comprehension | [Families and slices](FamiliesAndSlices.md) | [CwFs](CwFDesign.md) and [representation](CwFRecovery.md) |

## Selected constructions

### Category Theory

- [Categories](../../theories/Cat/Core.v) carry setoids of morphisms. Composition respects their specified equality.

- [CCC](../../theories/Cat/CCC/Core.v), [Topos](../../theories/Topos/Core.v) and
  [ETCS](../../theories/Topos/ETCS.v) extend the theory with chosen universal constructions.

- [Universes of structured categories](StructureUniverses.md):
  cartesian categories form a cartesian category, and groupoids with
  equivalences form a groupoid, with self-membership across universe levels.

- In the [category of sets](../../theories/Instance/Set/Core.v), objects are setoids and arrows are respectful maps.

- The Yoneda lemma is proved as a setoid isomorphism, with naturality equations
  in the representing object and the set-valued functor
  [see here](../../theories/Instance/Set/Yoneda.v).

- Explicit setoid models cover binary/indexed products and coproducts,
  equalizers/coequalizers, pullbacks/pushouts and finite, finitely generated,
  graph-generated and size-bounded general diagram limits/colimits.
  See [the models and their universe bounds](SetModels.md).

- [CCC structural theory](CCCStructure.md) provides canonical exponential
  isomorphisms and their naturality, limit preservation, cartesian closed functor
  composition, internal hom equations and native hom-setoid correspondences.

- [Groupoids](../../theories/Cat/Groupoid/Core.v) extend existing categories by
  invertibility of every arrow. Inverse coherence is derived from uniqueness;
  [functor and equivalence laws](../../theories/Cat/Groupoid/Functor.v) and the
  [thin equality groupoid of a setoid](../../theories/Instance/Set/Groupoid.v)
  retain specified equality and independent carrier/witness universes.
  [Setoid groups](../../theories/Algebra/Group/Core.v) give
  [single-object groupoids](../../theories/Algebra/Group/Category.v).
  The [boolean xor group and its action](../../theories/Instance/Bool/Action.v)
  provide a non-thin example whose nonidentity loop swaps boolean elements;
  its regular action reuses the covariant Hom functor.
  [Coherent families are equivalent to equality-groupoid actions](../../theories/Instance/Set/Fam/Groupoid.v),
  with reindexing corresponding to precomposition. Composing this comparison
  with Family-Slice gives an
  [equivalence between actions and slices](../../theories/Instance/Set/Fam/GroupoidSlice.v)
  under the existing Family-Slice size bound.

- The [simplex category](../../theories/Cat/Shape/Simplex/Core.v) reuses finite
  ordinal categories and the induced-category construction. Natural-isomorphism
  equality of its arrows is equivalent to pointwise equality of positions.
  [Cofaces and codegeneracies](../../theories/Cat/Shape/Simplex/Operators.v) use
  bounded finite indices and satisfy the simplicial identities.
  [Simplicial setoids](../../theories/Instance/Set/Simplicial/Core.v) reuse the
  presheaf category; their
  [faces and degeneracies](../../theories/Instance/Set/Simplicial/Operators.v)
  inherit these identities by restriction.
  [Standard simplices](../../theories/Instance/Set/Simplicial/Standard.v) form a
  fully faithful Yoneda embedding, with maps from the standard n-simplex
  corresponding naturally to n-simplices. Explicit universe lifts keep small
  simplex operators compatible with larger setoid values.
  The [ordinal vertex comparison](../../theories/Instance/Set/Simplicial/Vertex/Ordinal.v)
  also realizes `Δ[n]` as the vertex nerve of the finite ordinal with
  specified position equality. The transparent natural isomorphism commutes
  with all simplex operators and identifies the two chosen interval points
  with the existing simplicial endpoints.

The [CCC theory](CCCStructure.md#ccc-modules-and-the-category-of-cccs)
separates its [complete bundle](../../theories/Cat/CCC/Core.v),
[structured functors](../../theories/Cat/CCC/Functor.v) and
[category of CCCs](../../theories/Cat/CCC/Category.v). `CCCCat` has CCC bundles
as objects, preserving functors as arrows and natural-isomorphism equality;
`CCCForgetF` is its faithful forgetful functor to `CatCat`.

### Topos and ETCS

`Topos` stores one chosen `CCC` with pullbacks and a subobject classifier.
Its classifier uses the inherited terminal object. Import `Cats.Topos.Core`
for elementary topos theory without well-pointedness, choice or a
natural-numbers object. Import `Cats.Topos.Sub` directly for the classifier
interface and its existing proofs. Optional natural-numbers structures live
in `Cats.Topos.Nat`, and the stronger set-theory bundle in `Cats.Topos.ETCS`.
All nineteen modules are under `Topos/`; there are no ETCS compatibility imports.
Characteristic arrows respect monomorphism equality, detect subobject
equivalence and turn pullback into precomposition. These laws need only a
chosen terminal object and classifier; [pullback monicity](../../theories/Cat/Subobject.v)
holds in any category for a supplied pullback square.
The optional [representation module](../../theories/Topos/Representation.v) uses
truth as the generic subobject and reuses the universal-element theorem
to represent the subobject functor by explicitly lifted classifier arrows.
For finite intersections, [SubobjectIntersection](../../theories/Cat/SubobjectIntersection.v)
uses binary products in the Type-valued subobject preorder category.
Its [inverse-image laws](../../theories/Instance/Set/SubobjectIntersection.v)
need only chosen pullbacks and preserve comparison-factor data.
The optional [conjunction module](../../theories/Topos/Conjunction.v) classifies
paired truth. It proves substitution and truth criteria, and transports
intersection classification and laws to predicates.
The optional [predicate order](../../theories/Topos/PredicateOrder.v) retains
entailment factors, proves substitution monotone, and identifies conjunction
as greatest lower bound.
The optional [implication module](../../theories/Topos/Implication.v) classifies
the equalizer of conjunction and first projection. It proves substitution,
the truth criterion and the Type-valued Heyting adjunction with conjunction.
Equalizers remain explicit choices; a topos obtains them from its products
and pullbacks through the existing finite-limit conversion.
The optional [universal quantifier](../../theories/Topos/Forall.v) classifies
the name of constant truth. It gives quantification over a fixed product
factor, commuting with context substitution and right adjoint to projection
substitution, with transparent entailment factors.
The optional [predicate categories](../../theories/Topos/PredicateCategory.v)
retain these factors as arrows and make substitution a functor, without
products or exponentials. The optional
[reindex comparisons](../../theories/Topos/PredicateReindex.v) use the general
preorder comparison bridge for identity, composition and base-arrow equality
natural isomorphisms, with unit and association diagrams in natural equality.
Adding products and exponentials, the
[projection adjunction client](../../theories/Topos/ForallAdjunction.v) applies
the general preorder bridge to assemble an actual right adjunction,
retaining the same transposes and quantifier evaluation counit.
The optional [bottom module](../../theories/Topos/Bottom.v) quantifies over truth
values to obtain false, the least predicate and least subobject in each
context. Inverse image preserves these subobjects; their initial structure
in the thin subobject category is explicitly enabled.
The optional [ambient initial object](../../theories/Topos/Initial.v) classifies
false on the terminal object, constructs its unique arrow to every object,
and proves strictness. Its derived `HasInitial` choice is explicitly enabled;
no initial-object axiom is added to Topos.
The optional [image construction](../../theories/Topos/Image.v) intersects the
internal family of predicates containing an arbitrary arrow. It gives its
least containing subobject and an actual epimorphic factor, with unique
mediators into other containing subobjects. The general
[image property and epi proof](../../theories/Cat/Image.v) stay outside Topos.
The optional [ambient coproducts](../../theories/Topos/Coproduct.v) take the join
of two images in a double power object. They construct binary injections,
copairs and their full universal property, then reuse the existing finite
coproduct theory with the derived initial object for finite discrete colimits.
These choices are explicitly enabled. General
[double-dual evaluation](../../theories/Cat/Exponential/DoubleDual.v) stays outside
Topos; no coproduct axiom is added.
The optional [coequalizer construction](../../theories/Topos/Coequalizer.v)
evaluates on predicates identifying a parallel pair and takes the image.
It retains actual descent and proves its full universal property. Its
[general equalizing-test construction](../../theories/Cat/Exponential/Equalizing.v)
stays outside Topos. The existing finite-colimit conversion then supplies
pushouts and all colimits of a shape with an explicit finite hom cover or
finite generating graph. All these derived choices are explicitly enabled.
The optional [implication laws](../../theories/Topos/ImplicationLaws.v) exchange
antecedents and eliminate a true antecedent, without exponentials.
The optional [disjunction module](../../theories/Topos/Disjunction.v) quantifies
common upper bounds using implication. Its transparent introductions and
least-upper-bound correspondence retain entailment factors; substitution,
monotonicity and the join laws reuse the same chosen data.

`ETCS` extends its stored `Topos` with well-pointedness, split epimorphisms and a
natural-numbers object, retaining the existing chosen initial-object field.
The single parent chain is `ETCS → Topos → CCC → CartCat → Cat`;
terminal-dependent fields all use that same inherited choice. The optional
[initial-object theorem](../../theories/Topos/Initial.v) now derives an initial
object from the Topos structure; this batch preserves the existing ETCS field.

## Repository layout

- [Algebra](../../theories/Algebra/): setoid monoids and groups, their single-object
  categorical interpretations, endomorphism structures, and regular actions.
  The algebraic core modules depend on foundational sets, not categories.
- [Set](../../theories/Set/): foundational sets with designated Type-valued equality.
  [Core](../../theories/Set/Core.v) defines `SetC`;
  [Morphism](../../theories/Set/Morphism.v) defines respectful maps and function sets.
  This layer does not depend on categories; see the
  [foundation and migration note](FoundationalSets.md).
- [Cat](../../theories/Cat/): categorical interfaces and general constructions.
  Topic extensions are grouped under [Arrow/](../../theories/Cat/Arrow/),
  [Slice/](../../theories/Cat/Slice/) and [Bicategory/](../../theories/Cat/Bicategory/),
  alongside their core modules. [Shape/](../../theories/Cat/Shape/) contains index
  categories; [Diagram.Shape](../../theories/Cat/Diagram/Shape.v) collects diagram
  constructors grouped by mathematical subject.
  [Core](../../theories/Cat/Core.v) contains categories, duality, product categories,
  and isomorphisms. Each hom is a `HomSet : SetC`; `Hom` and `HomEq` are derived.
  Universal constructions are provided separately by
  [Terminal](../../theories/Cat/Terminal.v) (including initial objects),
  [Product](../../theories/Cat/Product/Core.v),
  [Exponential](../../theories/Cat/Exponential/Core.v), and
  [Pullback](../../theories/Cat/Pullback.v).
  [Slice](../../theories/Cat/Slice/Core.v) constructs `C /C X`, with commuting triangles
  up to morphism equivalence and equality on their underlying arrows.
  [Arrow](../../theories/Cat/Arrow/Core.v) constructs `Arr C`, with commuting squares,
  domain/codomain functors, and the functor induced by a natural transformation.
  [Section](../../theories/Cat/Section.v) defines `Sec(p)` for any category,
  retaining right-inverse witnesses and comparing the section maps. It maps
  sections along commuting maps over a base (`f ▷Sec[H] s`) and pulls them
  back along a given universal square (`s[HP]Sec`).
  [Slice.Reindex](../../theories/Cat/Slice/Reindex.v) gives pullback functors on slices,
  with specified natural identity and composition comparisons; write `A[f]C`.
  [Slice.Arrow](../../theories/Cat/Slice/Arrow.v) embeds slice maps as squares over the
  identity. Write `A^Arr` for the arrow object. Slice reindexing, including its
  unit/composition comparisons, agrees with codomain cartesian factorization
  for the same chosen pullbacks; `SliceReindexSquareN f` packages the natural squares.
  [Fct](../../theories/Cat/Functor/Core.v) and
  [Natural](../../theories/Cat/Natural.v) extend opposition to functors (`F ^opF`)
  and natural transformations (`α ^opN`). Functors are compared by natural
  isomorphism (`F ≅N G`), without requiring equality of their object values.
  Whiskering is written `G ∘Nl α` and `β ∘Nr F`; composition, fixing arguments,
  and taking opposites preserve natural isomorphisms.
  [Diagram.Dual](../../theories/Cat/Diagram/Dual.v) provides cocones `D ⇒∇ X`
  and their correspondence with opposite cones.
  [Colimit](../../theories/Cat/Colimit/Core.v) reuses opposite limits, with
  [diagonal adjunctions](../../theories/Cat/Colimit/Adjunction.v) and
  [left-adjoint preservation](../../theories/Cat/Colimit/Preservation.v);
  [initial objects](../../theories/Cat/Colimit/Initial.v),
  [coproducts](../../theories/Cat/Colimit/Coproduct.v),
  [coequalizers](../../theories/Cat/Colimit/Coequalizer.v) and
  [pushouts](../../theories/Cat/Colimit/Pushout.v) have corresponding
  colimit characterizations and explicit conversions of chosen structures.
  Write `X ⊔ Y`, `⦗f,g⦘`, `Coeq[f,g]` and `πcoeq[f,g]` for the ordinary
  interfaces to opposite products and equalizers. Pushouts use
  `X ⊔[f,g] Y`, `ιpo1[f,g]`, `ιpo2[f,g]` and `po⟨i,j,H⟩`.
  The [finite-colimit bases](../../theories/Cat/Colimit/Finite.v) convert between
  initial objects with pushouts and initial objects with coproducts and
  coequalizers, and construct colimits of finite or finitely generated shapes.
  [Indexed coproducts](../../theories/Cat/Coproduct/Indexed.v) use `∐[D]`,
  `ι∐[D]` and `∐⟨κ⟩`, with
  [finite](../../theories/Cat/Coproduct/Finite.v) and
  [dependent-index](../../theories/Cat/Coproduct/Sigma.v) constructions.
  [General diagram colimits](../../theories/Cat/Colimit/Construction.v) and
  [generator-based colimits](../../theories/Cat/Colimit/Graph/Core.v) reuse the
  opposite product/equalizer theory. Colimits also support
  [transport](../../theories/Cat/Colimit/Transport.v) and
  [shape reindexing](../../theories/Cat/Colimit/Reindex.v);
  see the [duality guide](Duality.md).
  [CatCat](../../theories/Cat/CatCat.v) provides the category of categories with
  this morphism equivalence. Write `C ≃C D` for an equivalence with chosen
  quasi-inverse functors and natural isomorphisms for the two composites.
  The double-opposite comparison is a natural isomorphism whose component
  functors act as identities on objects and morphisms.
  [Bicategory](../../theories/Cat/Bicategory/Core.v) introduces hom-categories, horizontal
  composition, interchange, and coherent associators/unitors.
  [Bicategory.Strict](../../theories/Cat/Bicategory/Strict.v) expresses strictness relative to
  a specified 1-cell equivalence (`f ≈₁[R] g`), with coherent comparison
  2-cells and strict associators/unitors. Write `α⟦p, q⟧₂` for transport of
  both endpoints of a 2-cell along specified 1-cell equivalences.
  [Bicategory.Thin](../../theories/Cat/Bicategory/Thin.v) gives a locally thin strict model
  from any category, retaining its morphism-equivalence witnesses as 2-cells.
  [Bicategory.Cat](../../theories/Cat/Bicategory/Cat.v) retains all natural
  transformations as 2-cells and proves pentagon/triangle coherence. `CatCat`
  remains its separate one-dimensional shadow up to natural isomorphism.
  [Bicategory.Homotopy](../../theories/Cat/Bicategory/Homotopy.v) constructs this shadow for any
  bicategory; the shadow of `CatBicat` is explicitly equivalent to `CatCat`.
  [The design note](TwoCategories.md) explains the levels of equality
  in this bicategory presentation. The small
  [natural-number model](../../theories/Instance/Nat/TwoCat.v) has
  noninvertible 2-cells and satisfies this setoid strictness interface.
  [Fibration](../../theories/Cat/Fibration.v) defines cartesian morphisms by universal
  factorization, compares lifts over a base isomorphism, and provides chosen
  cartesian lifts with explicit base-object identifications.
  [Arrow.Fibration](../../theories/Cat/Arrow/Fibration.v) proves that cartesian arrows
  of the codomain functor are precisely pullback squares. Chosen pullbacks and
  chosen codomain lifts yield one another by explicit constructions; write
  `B[σ]Arr` for the pullback arrow object. Both choices require explicit activation.
  [Comprehension](../../theories/Cat/Comprehension.v) combines chosen lifts with a
  total-space functor and a natural projection, requiring cartesian morphisms
  to give pullback squares. Write `A ^ext[K]` for the extension and `π[K] A`
  for its display projection. `ComprehensionF K` is its functor to the arrow category;
  fullness and faithfulness are separate properties.
  `RestrictedComprehension` restricts along an interpretation that preserves
  cartesian arrows, with a natural base isomorphism and explicit target lifts.
- [Instance/Set](../../theories/Instance/Set/): concrete implementations using setoids
  as sets. [Core](../../theories/Instance/Set/Core.v) defines their category `SetCat`;
  [Product](../../theories/Instance/Set/Product.v),
  [Pullback](../../theories/Instance/Set/Pullback.v), and
  [Fam](../../theories/Instance/Set/Fam/Core.v) provide independent extensions.
  [FamCat](../../theories/Instance/Set/Fam/Cat.v) assembles coherent families and
  transport-compatible maps into a category, with base and total-space
  functors to `SetCat` and their natural projection.
  [FamLift](../../theories/Instance/Set/Fam/Lift.v) raises fiber carriers and
  equality witnesses independently, preserving the base and coherent transport.
- [DTT](../../theories/DTT/): dependent type theory interfaces.
  [Display](../../theories/DTT/Display/Core.v) specifies coherent display maps over a
  type presheaf, with designated-equality conversion and chosen display pullbacks.
  [Context/Display](../../theories/DTT/Context/Display.v) constructs this choice from
  context extensions, without requiring a terminal object or arbitrary pullbacks.
  [Display/Section](../../theories/DTT/Display/Section.v) constructs `DisplayTyTmF P`
  in the reverse direction: terms are sections of the display projections,
  conversion is `e ▸D[P] s`, and substitution is `s[σ]TmD[P]`.
  [Display/Representation](../../theories/DTT/Display/Representation.v) proves
  universality of the display pair and reuses the general lifted Hom theory
  for its representation. It recovers context extensions and constructs
  `DisplayCwF P` with a separately chosen terminal context; model selection
  remains explicit. Derived context conversion and substitution lifts agree
  with the supplied display maps in specified hom equality.
- [Topos](../../theories/Topos/): elementary topos structure and classifiers,
  with separate optional natural-numbers and

Chosen universal constructions share the same design: `is_*` describes a
specific candidate, and `Has*` stores a chosen candidate with that universal
property. Mediating maps are extracted from transparent witnesses; their laws,
uniqueness, and respectfulness follow from the property. This covers
[products](../../theories/Cat/Product/Core.v),
[terminal and initial objects](../../theories/Cat/Terminal.v),
[exponentials](../../theories/Cat/Exponential/Core.v),
[pullbacks](../../theories/Cat/Pullback.v),
[natural-numbers objects](../../theories/Topos/Nat.v), and
[subobject classifiers](../../theories/Topos/Sub.v).

Loading the setoid terminal or product module registers its standard instance.
Other choices, such as pullbacks, can be enabled locally.

```coq
From Cats Require Import Instance.Set.Core.
From Cats Require Import Instance.Set.Product Instance.Set.Pullback.

Local Existing Instance SetCat_HasPullback.
```

The complete cartesian closed model packages the chosen category and its structure. Pass it to clients
that take a CCC.

```coq
From Cats Require Import
  Cat.CCC.Core
  Instance.Set.CCC.

Definition chosen_model
  : CCC
  := SetCat_CCC.
```

The [CCC/STLC research note](CCCAndSTLC.md) explains the interpretation
of simple types, contexts, substitution and βη equations in an arbitrary CCC.
The reusable [exponential laws](../../theories/Cat/Exponential/Core.v) and
[hom-setoid correspondence](../../theories/Instance/Set/ExponentialHom.v) are implemented;
the general [adjunction theory](../../theories/Cat/Adjunction.v) starts with natural
hom isomorphisms and derives unit/counit and composition, including `(-) × A ⊣ (-)^A`.
The optional [preorder adjunction bridge](../../theories/Cat/Logic/Adjunction.v)
turns a Type-valued relation correspondence into this existing adjunction
interface, retaining its witness maps. It supports independently sized
preorder categories and specializes through `PreorderF`; it is independent
of Topos and does not assume classifiers, limits or a full hyperdoctrine.

The optional [preorder comparison bridge](../../theories/Cat/Logic/Natural.v)
assembles pointwise witnesses into natural transformations and mutual
comparisons into natural isomorphisms. Its source category is arbitrary;
only the target uses the existing thin preorder model. Forward/inverse
components retain their chosen data, and parallel transformations compare
by the existing `NatEq`, without native equality of witnesses.

The [limit theory](Limits.md) derives limit functors, the diagonal
adjunction and preservation of limits by right adjoints from universal properties.
The [graph and free-category constructions](Graphs.md) generate diagram
shapes and identify binary products and pullbacks with their corresponding limits.
The [small-category catalogue](SmallCategories.md) also provides arrows,
spans, parallel pairs, commuting squares, walking isomorphisms and finite ordinals.
Empty and parallel-pair limits are identified with terminal objects and
equalizers; all four shape correspondences derive right-adjoint preservation
from the general limit theorem.
The [finite-limit basis constructions](../../theories/Cat/Limit/Finite.v) convert
terminal objects and pullbacks to terminal objects, binary products and
equalizers, and conversely, with explicit chosen structures.
The [general limit construction](../../theories/Cat/Limit/Construction.v) uses
the equalizer of two maps between object-indexed and arrow-indexed products;
indexed products reuse discrete limits directly.
The [finite product construction](../../theories/Cat/Product/Finite.v) derives
limits of finite discrete diagrams from terminal objects and binary products,
using shared [finite positions](../../theories/Set/Finite.v).
The [generator-based construction](../../theories/Cat/Limit/Graph/Core.v) needs products
only over vertices and generating edges. Its
[finite-graph specialization](../../theories/Cat/Limit/Graph/Finite.v) derives limits
from terminal objects, binary products and equalizers, including shapes with cycles.
The [shape-transfer theorem](../../theories/Cat/Limit/Reindex.v) transfers limits
along full, essentially surjective functors, using object isomorphisms and
specified hom equality without requiring faithfulness.
The [cone presheaf comparison](../../theories/Cat/Diagram/Presheaf.v) packages
restriction and extension as an explicit natural setoid isomorphism in the
apex, with a specialization to chosen finite generators.
[STLC.Free](../../theories/STLC/Free.v) provides the completed syntax/semantics result:
interpretation in arbitrary CCCs, semantic substitution, βη soundness and
completeness at a common bound containing the syntax model. Its free-CCC
universal property extends specified base-type isomorphisms to unique natural
transformations, with invertible canonical extensions.
[ContextEquivalence](../../theories/STLC/ContextEquivalence.v) identifies the context
and type presentations. See [#9](https://github.com/Godalin/rocq-cats/issues/9)
and [#20](https://github.com/Godalin/rocq-cats/issues/20) for acceptance records.
