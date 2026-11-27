# Monad Applicative and Arrow audit

Historical audit. Names, implementation choices and validation results below refer
to their recorded revisions. For current authoring rules, see the
[mathematical interface guide](../development/HierarchyDevelopment.md).


Source-pinned evidence below retains its historical identifiers. See the
[abbreviation map](../development/Abbreviations.md) for their current public names.

[Issue #35](https://github.com/Godalin/rocq-cats/issues/35) starts with a
source-level prior-art audit. The first implementation slice is **lax monoidal
transport of monoid objects and homomorphisms** (milestones B and G). This is
an existing mathematical result, with an existing Lean formalization; its
purpose here is integration with the library's Type-valued setoid equality
and independent universes. No formalization-priority claim is made.

## Revisions and evidence

Sources were read on 2026-11-09 at the following fixed revisions. The audit
checks declarations and proof bodies, not just module names or explanatory
comments. Third-party projects were not compiled and their transitive axioms
were not kernel-audited. “Not established” below describes the checked source,
not a claim that no such theorem exists anywhere in the project.

| Project | Revision |
| --- | --- |
| [jwiegley/category-theory][w] | `99869fd8d9117e900dea862d8612033848aa01dd` |
| [Lean mathlib4][m] | `9bac2d0692944a775113f7c130fd5e5b4608a854` |
| [Lean core][l] (mathlib's pinned toolchain) | `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a` (`v4.36.0-rc2`) |
| [agda/agda-categories][a] | `ade267a5a02688fb97ec9d6e03ab6192be94439e` |
| [UniMath/UniMath][u] | `7a4b03cce49449f45ce0d4285615165172f50546` |
| Rocq-Cats integration baseline | `8ae7cbd9f09c1738e9e30f4c637004552338036d` |

The tables retain the issue's eight evidence columns. Equational laws of
operations are distinguished from preservation/reflection of a typed
syntactic equational theory.

| Project/commit | Directly checked module/theorem | Laws included | Categorical characterization | Structural conversions | Equational theory results | Extra axioms/size constraints | Missing lemmas or compatibility boundary |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Wiegley `99869fd` | [Theory/Coq/Applicative.v][w-app]; [Applicative/Proofs.v][w-app-proofs]: `IsApplicative`, `EndoApplicative_Applicative`, `Identity_IsApplicative`, `arrow_IsApplicative`, `Compose_IsApplicative` | The operation class stores `pure` and `ap`, without law fields; separate categorical witnesses for named instances | `IsApplicative` returns the categorical `Applicative` structure on `ToAFunctor H` | Categorical structure → operations; identity, reader and composite witnesses | Computation lemmas; no typed three-way translation theorem in these declarations | Coq-type/function model; the checked `arrow_IsApplicative` proof uses `extensionality`; [Coq model][w-coq] documents its funext boundary | `IsApplicative`'s result does not mention its supplied operation instance: it alone does not prove that arbitrary supplied `pure`/`ap` agree with the categorical operations |
| Wiegley `99869fd` | [Functor/Applicative.v][w-capp]; [Monoidal.v][w-lax]; [Monoidal/Pure.v][w-pure]: `Applicative`, `LaxMonoidalFunctor`, `pure_natural`, `fmap_pure` | Tensorator naturality, two unit laws, associativity; naturality of strength-derived `pure` | Bundles tensorial strength and lax monoidal structure over a closed monoidal base | `pure` from unit comparison and strength; `ap` from tensorator and evaluation | Naturality rewrites; the four conventional `ap` laws are not proved by the checked `Applicative` declaration | Arbitrary categories with specified hom equality; `LaxMonoidalFunctor` additionally stores `pure_left`, `pure_right`, `ap_assoc` **isomorphisms** | In particular `ap_assoc : (F X ⊗ F Y) ⊗ F Z ≅ F (X ⊗ (Y ⊗ Z))` is extra data, not part of the minimal lax interface; compatibility between strength and tensorator needs separate attention |
| Wiegley `99869fd` | [Monad/Strong.v][w-strong]; [Kleisli/Premonoidal.v][w-kprem]; [Premonoidal/Freyd.v][w-freyd]: `StrongMonad`, `dstr`, `dstr'`, `Freyd_Kleisli`, `Freyd_Id` | Strength coherence and compatibility with unit/multiplication; premonoidal and centrality laws | Kleisli computations with separately functorial tensoring; central pure inclusion | Strong monad on a symmetric monoidal base → Kleisli premonoidal structure and the file's `Freyd` | Structural preservation lemmas; no computational Arrow syntax equivalence established here | Tensorial strength is input; `Freyd` uses native object equalities and transported identities | The source explicitly omits cartesian values, symmetric premonoidal structure, and symmetry preservation from `Freyd`; its result is an effectful-category interface, not the full classical Freyd characterization |
| Wiegley `99869fd` | [Construction/Day.v][w-day]: `Day`, `Day_Tensor`, `lu_iso`, `ru_iso`, `day_assoc_iso`; [Sets/Coend.v][w-coend]: `SetsCoend` | Functor laws, natural unitors and associator, inverse laws | Covariant setoid-valued Day convolution via generated coend equality | Coend mediators and natural maps in both arguments | Pointwise/setoid coherence ingredients, not an Applicative/Day equivalence | Concrete coend equality is inductive in `Type`; output size must accommodate object-indexed sums and homs | The checked file explicitly defers the packaged monoidal structure and its pentagon/triangle proofs; do not infer them from the existence of `day_assoc_iso` |
| Wiegley `99869fd` | [Theory/Profunctor.v][w-prof]; [Compose.v][w-prof-comp]; [Laws.v][w-prof-laws]: `Profunctor`, `prof_compose`, `prof_unit_left_iso`, `prof_unit_right_iso`, `prof_assoc_iso`; [Cayley.v][w-cayley]: `To_Cayley`, `From_Cayley` | Profunctor functor laws and composition unit/associator isomorphisms; Cayley functor laws | Profunctors are `Cᵒᵖ × D → Sets`; Cayley is a category-level Yoneda-style representation | Profunctor composition; category-to-Cayley and evaluation back | `Cayley_Left`/`Cayley_Right` reassociate composition | Profunctors are kept in per-pair functor categories for universe reasons | Composition laws defer a bundled bicategory; ordinary profunctors do not supply strong promonads. Category-level Cayley is not the paper's internal-hom monoid representation |
| Lean/mathlib `9bac2d0`; core `b35cb10` | [Init/Control/Lawful/Basic.lean][l-lawful]: `LawfulApplicative`, `LawfulMonad`; [Control/Applicative.lean][m-app]: `instLawfulApplicativeComp`, lawful `Const` | Functor compatibility, `pure_seq`, `map_pure`, `seq_pure`, `seq_assoc`; Monad laws supply inherited Applicative laws | Lawful operations on type constructors | Lawful Monad includes lawful Applicative; lawful composition and constant applicatives | Actual operation equalities, not merely operation instances; no three-way categorical syntax comparison here | Law witnesses live in `Prop`; native equality and Lean extensionality/proof-irrelevance regime, not Type-valued setoid witnesses | An adapter to a generic categorical lax interface and preservation/reflection of Arrow calculi are separate obligations |
| Lean/mathlib `9bac2d0` | [Monoidal/Functor.lean][m-lax]: `Functor.LaxMonoidal`, `Functor.OplaxMonoidal`, `Functor.Monoidal`; [Monoidal/Mon.lean][m-mon]: `monObjObj`, `map.instIsMonHom`, `mapMon`, `mapMonIdIso`, `mapMonCompIso` | Tensorator naturality and three coherences; transported monoid and homomorphism laws; functor laws | Lax monoidal functors preserve monoid objects | Full functor on monoid-object categories; identity/composition comparison isomorphisms | Preservation of unit/multiplication by mapped homomorphisms | Independent object/hom universes; laws use native equality in `Prop` | This already covers the mathematical content of milestone B's transport theorem; Rocq-Cats needs integration with its own equality and universe discipline |
| Lean/mathlib `9bac2d0` | [DayConvolution.lean][m-day]: `DayConvolution`, `LawfulDayConvolutionMonoidalCategoryStruct`, `monoidalOfLawfulDayConvolutionMonoidalCategoryStruct`; [Closed.lean][m-day-closed]: `DayConvolutionInternalHom` | Chosen pointwise left Kan extensions, coherence for selected convolution structures; internal-hom/end data | General monoidal targets, not only endofunctors on types | Promotes suitable lawful data to monoidal structure | No lawful Applicative ↔ Day-monoid ↔ computational Arrow diagram established by these declarations | Requires selected extensions and tensor preservation of the stated colimits; internal homs additionally require ends and closedness | The source lists a lax-monoidal universal characterization and the `Type` case as TODOs; closed module also has an instance-packaging TODO. Read theorem bodies rather than treating every header TODO as current coverage |
| Agda `ade267a` | [Functor/Monoidal.agda][a-lax]: `IsMonoidalFunctor`, `IsStrongMonoidalFunctor`; [Monad/Strong.agda][a-strong]: `Strength`, `StrongMonad`; [Object/Monoid.agda][a-mon]: `IsMonoid`, `Monoid⇒`; [Construction/Kleisli.agda][a-kl] | Tensorator naturality, unit/associativity; strength and monad compatibility; monoid/homomorphism laws | Setoid-style hom equality with separate `o`, `ℓ`, `e`; lax vs strong distinguished | Strong → lax forgetful construction; monoidal Kleisli construction takes a **commutative** monad over a symmetric base | Certified diagrams; no three-way typed equational comparison in the inspected modules | All four inspected modules use `--safe --without-K`; joined levels bound records | Monoidal Kleisli under commutativity is stronger than the premonoidal Kleisli result needed for sequential effects; do not impose commutativity on all computational Arrows |
| UniMath `7a4b03c` | [Monoidal/Functors.v][u-lax]: `lax_monoidal_functor`, `make_lax_monoidal_functor`; [StrongMonad.v][u-strong]: `left_strength`, `left_strong_monad`; [CategoriesOfMonoids.v][u-mon]: `MON`; [Monads/Kleisli.v][u-kl]; [MonadsAsMonoidsElementary.v][u-mm] | Monoidal functor coherence; strength, unit/multiplication compatibility; monoid category laws | Hom-sets with identity-type equality; monad/monoid framework | Kleisli triple → Monad; endofunctor-monoid development | Structural equations; no three-way typed syntax theorem established here | UniMath foundations and hom-set truncation; strength-law propositionality explicitly uses `impred` and `homset_property`; transitive axiom usage not audited | This foundation is not a drop-in replacement for proof-relevant designated setoid equality; a bridge and the direct computation comparisons remain separate work |

The most important compatibility gaps are therefore substantive: operation
instances without laws, extra invertibility requirements in a purported lax
interface, missing compatibility with supplied operations, incomplete Day
coherence packaging, and a Freyd interface weaker than its classical name.
None of these establishes a new theorem merely by being absent from one
checked module.

## Paper coverage and local reuse

The paper snapshot is [arXiv:1406.4823v1][paper], submitted 2014-05-29.
Its TeX source directly supplies the statements labelled `thm:monoid`
(the issue's Theorem 8.1) and `thm:Cayley` (the issue's Theorem 2.9).
This audit does not establish that all numbering and hypotheses coincide
with the 2017 journal version. The paper's associator orientation must also
be translated to this library's chosen orientation.

| Paper statement | Assumptions | Local theorem or prerequisite | Checked third-party evidence | Verification gap |
| --- | --- | --- | --- | --- |
| Lax functors preserve monoids (`thm:monoid`) | Two monoidal categories; unit comparison, natural tensorator, three coherences | [LaxMonoidObject, lax_monoid_hom and LaxMonoidF](../../theories/Cat/Monoidal/Transport.v) reuse [MonoidObject and MonoidCat](../../theories/Cat/Monoidal/Monoid.v) | mathlib `monObjObj`, `mapMon`, `mapMonCompIso` | Object and homomorphism transport implemented; identity/composition comparison of transport in the lax functor remains separate work. No closedness, strength, symmetry or coends required |
| Generalized Cayley (`thm:Cayley`) | A monoid whose carrier is exponentiable for the required tensor order; a chosen right internal hom is sufficient | General monoidal closed structure still needed; [CCC internal hom](../../theories/Cat/Exponential/InternalHom.v) is a cartesian client | Wiegley's `Construction/Cayley.v` is category-level, not this statement | Endomorphism monoid; monoid homomorphism `rep`; ambient retraction `abs ∘ rep ≈ id`; do not claim `abs` preserves multiplication |
| Free monoid objects | Suitable countable coproducts, tensor preservation and explicit size/coherence data | Reuse [colimit theory](../../theories/Cat/Colimit/Core.v) and [free-object interface](../../theories/Cat/FreeObject/Core.v) where applicable | Not audited as an exact theorem in this slice | Specify sufficient existence assumptions before construction; neither a free monoidal category nor a free monad is this theorem |
| Monad as a monoid | Endofunctor category under composition | Already proved: [monad_monoid_laws and monad_monoid_equiv](../../theories/Cat/Monad/Monoid.v); [is_monad](../../theories/Cat/Monad/Core.v) already exists | Wiegley and UniMath have relevant developments | Reuse the existing presentation; no second Monad definition |
| Applicative as a Day monoid | Correct Day tensor, unit, coherence and size/existence conditions; strength when required | Direct lax/operation interfaces precede any new coend theory | Wiegley's Day ingredients; mathlib's selected Kan-extension formulation | Build the actual correspondence and law preservation; a module named Day is insufficient |
| Arrow as a strong profunctor monoid | Strong profunctors, chosen composition/coends, unit and associativity coherence | No computational Arrow interface in this baseline; [Cat/Arrow](../../theories/Cat/Arrow/Core.v) is the ordinary arrow category | Wiegley's profunctor composition and weakened Freyd presentation | Strong promonads, full Arrow/Freyd correspondence and exact typed equational statements remain |

## Lawful Applicative slice

The serial continuation after `1495819` adds
[Applicative](../../theories/Cat/Applicative/Core.v) over a named category,
terminal object and binary products. It stores one cartesian lax monoidal
endofunctor and a natural pure map. Its two additional laws identify the pure
terminal component with the lax unit and identify the pure product component
with tensorial combination of pure components. Thus the pure map is monoidal.
No exponential structure is required by this interface. The unique coercion
chain is `Applicative → LaxMonoidalFct → Fct → object function`;
arrow maps retain `fmap`, and concrete choices remain explicit.

The current record migration exposes the direct
`ApplicativeOfLaxMonoidalFct` constructor and the unique
`ApplicativeToLaxMonoidalFct` parent projection. It keeps the selected
lax functor, pure map and compatibility laws together. `SetLaxA` still
recovers pure values only in the native setoid model; the general category
interface retains its supplied natural pure map. The complete record is
not a typeclass and importing it does not select a concrete Applicative.

[Binary lifting](../../theories/Cat/Monoidal/Lifting.v) is first developed for
arbitrary lax monoidal functors and operations. Naturality, unary-map
substitution and preservation of general associativity diagrams do not use
pure values or exponentials. This supplies the reusable argument behind
Applicative composition. The shared
[internal composition evaluation lemma](../../theories/Cat/Exponential/InternalHom.v)
comes from the existing exponential beta law and product associator.

With chosen exponentials, [application](../../theories/Cat/Applicative/Closed.v)
is lifted evaluation. The proved classical laws are identity, homomorphism,
interchange and composition, including the curried pure composition followed
by three applications. All allow a shared arbitrary context. Homomorphism
allows both pure inputs to vary in that context; the pure function in the
mapping law and the pure argument in interchange are fixed global values
pulled back into the context. The equations use designated hom equality and
retain Type-valued witnesses; they do not equate functor or law records.

The explicitly selected [ReaderA](../../theories/Instance/Set/Reader.v)
uses respectful maps, constant functions and pointwise pairing. Postcomposition
reuses the foundational composition laws. Its environment equality level is
separate, and a small environment permits the ambient carrier universe to be
strictly larger than the equality universe. Temporary checks instantiate the
abstract interface and application at both strict hom/equality universe
orders and check transparent Reader pure/map/pair/application computation.

This is a sufficient lawful Applicative presentation, not a claim that an
arbitrary cartesian lax endofunctor determines a natural pure map. The reverse
construction from coherent operation interfaces is described below. Tensorial
strength and its compatibility laws, Monad conversion and computational Arrow
are delivered in the later slices below. The Reader model does not impose
size bounds on the abstract interface. No general coend or Day convolution
construction is introduced by this slice.

The existing `rocq-cats` switch (Rocq/Stdlib 9.2.0, Dune 3.23.1) passed
`dune build @all @runtest @install`. Twenty-nine temporary assumption checks
for lifting, pure/application laws, internal composition, the Reader model
and its computations all reported `Closed under the global context`.
Strict bilingual HTML export generated 260 modules per language and checked
links and anchors in 525 pages. New interface explanations were inspected in
both languages. No permanent test source or shared test alias was added;
batch PDF export remains with the integration session.

## Coherent operation presentations and reconstruction

[ApplicativeOps](../../theories/Cat/Applicative/Operations.v) independently
stores an endofunctor, a natural pure map and a binary lifting operation.
Its fixed-data law class `IsApplicativeOps` requires respectfulness, result
and input substitution, preservation of pure pairs, left/right terminal
units and preservation of associativity diagrams with different intermediate
types. Every equation is an equation of arrows, not merely of global values.
No exponentials are required. The lifted identity on a product reconstructs
the tensorator; the pure terminal component reconstructs the unit comparison.
`OperationsA` proves the lax and pure compatibility laws from these operations.

With chosen exponentials,
[ApplicativeAp](../../theories/Cat/Applicative/Application.v) stores only the
endofunctor, natural pure map and application family. Currying, functorial
mapping and application reconstruct binary lifting. Its laws explicitly
require this reconstructed lifting to satisfy `IsApplicativeOps`.
`ApplicationA` then reconstructs the structural Applicative. Conversely,
lifting evaluation exposes application, and input substitution plus the
exponential beta law recover every original binary operation. A general
pointwise transport lemma transfers the fixed-data operation laws; it does
not equate functions or proof fields.

All conversions retain the underlying functor by computation and preserve
pure, binary lifting, application, tensorator and unit as applicable, using
designated hom equality. Application preservation also holds in arbitrary
shared contexts, so rewriting it and pure preservation transfers the four
classical laws from `ApplicationA`. These are coherent operation presentations:
no claim is made that four equations on global values alone supply all the
naturality/coherence data in an arbitrary CCC. These particular conversions
need no additional tensorial strength. The general tensorial-strength
foundation, strong-monad conversion and computational Arrow are described
below.
No Day convolution or extra model construction is introduced.

Validation uses the existing `rocq-cats` switch. Full-library build, tests
and installation passed. Temporary checks cover both strict hom/equality
universe orders, rewriting under the bundled operation, absence of implicitly
selected model instances, all four transferred classical laws over an abstract
CCC and ten transparent Reader computations through the conversions.
Seventy-seven temporary `Print Assumptions` checks reported
`Closed under the global context`, including the previous lifting/application
slice. Strict bilingual HTML export generated 262 modules per language and
checked links and anchors in 529 pages. Both languages of the new interface
explanations were inspected. The checks do not add permanent test sources or
shared test aliases. Batch PDF export remains with the integration session.

## Tensorial-strength foundation

[HasStrength](../../theories/Cat/Monoidal/Strength.v) chooses a natural map
carrying an ordinary left tensor context through an effectful right input,
with unit and associator coherence. Its base is a named monoidal structure,
not necessarily cartesian. It is distinct from an invertible tensorator.
[StrongMonad](../../theories/Cat/Monad/Strength.v) retains the existing ordinary
Monad as its unique underlying view and adds this chosen strength together
with compatibility with monad unit and multiplication. No commutativity,
closedness or implicit model selection is required.

[Kleisli extension](../../theories/Cat/Monad/Extension.v) and its unit,
substitution and associativity laws reuse the existing Monad operations.
Contextual extension in the strength module then transports an ordinary
tensor context through an effectful argument. Its associativity theorem
reassociates nested contexts and keeps effect order. This foundation is
independently reusable; the finite-product Applicative conversion below is
derived from these laws, rather than assumed as an extra field here.

The initial foundation slice passed the full build/test/install targets
with the existing `rocq-cats` switch. Temporary checks instantiated both
strict hom/equality universe orders and all 18 initial foundation assumption
checks were closed under the global context.
No permanent tests or shared environment changes were added.

## Strong Monad to ordered Applicative

[Contextual binding](../../theories/Cat/Monad/Context.v) specializes the general
strength extension to named finite products. Its endpoints expose those
products directly, and its equations cover equality, context substitution,
pure substitution, return, ordinary mapping and associative sequencing.
[Cartesian strength projection](../../theories/Cat/Monoidal/Cartesian.v)
uses only strength naturality and its unit law to discard an ordinary
context without changing the effectful input.

[MonadA](../../theories/Cat/Monad/Applicative.v) takes a `StrongMonad` over the
cartesian monoidal structure determined by the named terminal object and
products. It retains the underlying functor by computation and uses the
original monad unit as its natural pure map. Binary combination binds the
left computation, then the right, then returns their pair. Naturality,
both unit laws, associativity and pure-product compatibility are proved
from the binding laws. The contextual pairing equation `monad_pair_pre`
keeps computations stored in an ordinary context abstract during the proof;
all temporary proof opacity is restored. No strength for an arbitrary
functor, commutativity, exponential objects or invertible tensorator is
assumed. With chosen exponentials, the existing application construction
and four classical laws apply directly to `MonadA`.

The explicit [State model](../../theories/Instance/Set/State.v) supplies the
ordinary `StateM`, coherent `StateStrength` and `StateStrongM`; `StateA`
is derived solely by the general conversion. No second set of model-specific
Applicative laws is proved. State and ambient equality/carrier levels remain
separate, subject to the actual function-space/product size bounds.
Explicit ambient universe parameters prevent the natural transformations
from unnecessarily identifying the ambient carrier and equality levels.
Importing the model does not select a monad, strength or Applicative instance.

Temporary checks instantiate the abstract conversion and its application
at both strict hom/equality universe orders, compare underlying functors by
identity natural isomorphisms, and check state models with both strict state
carrier/equality orders and a larger ambient carrier. Seven transparent
Boolean-state computations cover pure, mapping, two pairing orders, repeated
state transitions, application and an application-interface round trip.
Toggling state before reading yields a different returned Boolean from
reading before toggling, witnessing the specified order. All 148 temporary
assumption checks, including the previous Applicative slice, are closed
under the global context. No permanent tests or shared test aliases were
added. The ordinary Kleisli category is delivered in the next slice below;
the strong-Monad Arrow comparison is delivered below. Freyd and
Day/profunctor characterizations remain separate work.

The final phase passed `dune build @all @runtest @install` using the existing
`rocq-cats` switch (Rocq/Stdlib 9.2.0, Dune 3.23.1). Strict bilingual HTML
export generated 269 modules per language and checked links and anchors in
543 pages; the new explanations were inspected in both languages. Batch PDF
export remains with the integration session.

## Ordinary Kleisli category

[KleisliCat](../../theories/Cat/Monad/Kleisli.v) takes only the existing
`Monad C`. It keeps the objects of `C`, reuses `HomSet X (M Y)` with its
specified Type-valued equality, chooses the monad unit as identity and
composes by Kleisli extension. Respectfulness, both unit laws and
associativity reuse the existing extension theory. No strength, products,
terminal object, exponentials or commutativity are needed.

`KleisliPureF` sends ordinary arrows to pure computations and keeps objects
unchanged; it is not asserted faithful. `KleisliExtendF` sends objects to
their Monad images and computations to their extensions. Their composite
is compared with the original endofunctor by `KleisliCompositeIso`, whose
components are identities. This is a comparison of endofunctors, without
equating function or law records. This initial comparison concerns only
endofunctors; the full Monad recovery is delivered below.
The public `g ∘K[M] f` notation names the same composition as the category;
pure-input and pure-output equations recover ordinary substitution and
result mapping.

Temporary checks cover both strict hom/equality universe orders with
arbitrary ordinary monads, inherited equality in both directions, rewriting
through composition, both functors and their natural isomorphism. Six
transparent state computations exercise sequencing, repeated transitions,
pure input/output and extension through the functor. All 34 assumption
checks for this slice are closed under the global context. The abstract
checks import only the Kleisli module and confirm strength interfaces are
unavailable. No permanent tests or model-specific category proofs were
added. Computational Arrow and its strength operations are delivered below;
Freyd remains later work.

This slice passed full-library build/tests/install with the same `rocq-cats`
switch. Strict bilingual HTML generated 270 modules per language and checked
545 pages; the new module's explanations and public constructions were
inspected in both languages. Batch PDF export remains with integration.

## Kleisli adjunction and recovery of the Monad

[KleisliAdj](../../theories/Cat/Monad/Kleisli.v) reuses the
general `AdjunctionFromHom` construction with identity respectful maps:
the two hom-sets are the very same base hom-set. Their inverse equations
are reflexivity, source naturality is pure substitution, and target
naturality is Kleisli composition. Forward and inverse transposition
preserve the underlying computation. The unit is the original Monad unit;
the counit at `X` is the base identity on `M X`, viewed as a Kleisli arrow
from `M X` to `X`. Both triangle laws are inherited from the general
adjunction theory. Only an ordinary Monad is supplied.

`KleisliMonad` uses the existing `AdjunctionMonad`, without a second proof
of its Monad laws. Its unit agrees with the original unit by computation;
its multiplication agrees in designated Hom equality, using preservation
of identities by the original functor. The previous identity-component
functor isomorphism and its inverse preserve unit and multiplication.
`KleisliMonadTo` and `KleisliMonadFrom` package these as fixed-base Monad
morphisms; `KleisliMonadIso` is their actual isomorphism in the existing
`MonadCat C`. This compares complete Monad structures without equality of
functor functions, category records or law witnesses. It does not assert
an equivalence between all adjunctions and all Monads.

Temporary checks cover both strict hom/equality universe orders and a
case with objects strictly larger than both, the recovery isomorphism,
operation rewriting, preservation by both Monad morphisms and transpose
rewriting. Six transparent state computations cover recovered return,
mapping, multiplication, counit and both comparison maps. All 52 assumption
checks for this slice are closed under the global context. Abstract probes
import only this module and confirm that strength and product interfaces
are unavailable. No permanent tests or concrete model proofs were added;
computational Arrow is delivered below and Freyd remains separate work.

This slice passed full-library build/tests/install with `rocq-cats`
(Rocq/Stdlib 9.2, Dune 3.23.1). Strict bilingual HTML generated 271 modules
per language and checked links and anchors in 547 pages; the new module's
explanations were inspected in both languages. Batch PDF export remains
with integration.

## Arrow foundation over a monoidal base

[Arrow](../../theories/Cat/Computational/Arrow/Core.v) now takes a named
monoidal base and a computation category, with a pure-arrow functor as
its unique underlying view. Its left-context action preserves pure maps
and composition, is natural in the ordinary context, and satisfies unit
and associator coherence. It assumes neither products nor symmetry nor
interchange of two effects. Computations live between images of the pure
functor; the existing `InducedCat` gives a presentation indexed by base
objects, and `ContextF` packages the action at a fixed context as a functor.

[PureArrow](../../theories/Cat/Computational/Arrow/Pure.v) uses ordinary left
tensoring. [KleisliArrow](../../theories/Cat/Computational/Arrow/Kleisli.v)
uses the chosen tensorial strength of an ordinary strong Monad, retaining
its existing Kleisli category and pure functor. These are explicit models.
The construction reuses strength compatibility and coherence rather than
proving laws separately in each concrete model. The Haskell-style cartesian
operations and ordered Applicative comparison are delivered below.

The independent foundation passed full-library build/tests/install with
the existing `rocq-cats` switch. All 26 temporary assumption checks are
closed under the global context. Probes cover both strict hom/equality
orders, independent base/computation sizes and the fixed-context functor;
importing the foundation alone supplies no product interface. No permanent
tests were added.

## Cartesian Arrow operations and ordered comparison

[Cartesian Arrow operations](../../theories/Cat/Computational/Arrow/Cartesian.v)
specialize the monoidal action to the named finite-product structure.
`second` is that existing action; `first` is derived by pure exchanges.
The pure identity/composition laws and the five classical `first` laws
(pure arrows, sequencing, projection, context naturality and associativity)
are proved, matching the seven basic laws in the official
[Control.Arrow documentation](https://hackage-content.haskell.org/package/base-4.20.0.0/docs/Control-Arrow.html#t:Arrow).
In particular, projection is derived from monoidal unit coherence and
naturality into the terminal context; it is not a new axiom. Ordered split
and fanout use context action and pure duplication; no joint bifunctoriality
or interchange of two effects is asserted. `Proper` supports rewriting all
these operations in the designated computation equality.

[The comparison](../../theories/Cat/Computational/Arrow/Applicative.v) uses
one chosen strong Monad. It rewrites Kleisli `first` and `second` by
contextual binding, proves split equals the previous `monad_pair` after
the two input computations, and proves fanout equals Applicative pairing
in every shared ordinary context. Specializing to computation-valued inputs
recovers exactly the tensorator of `MonadA`; pure lifting uses the same
return. This is a comparison of these constructions, not a conversion of
arbitrary Arrows into Applicatives. Two reusable binding equations and the
existing sequencing simplifier now live in `Cat.Monad.Context`; the old
Applicative proof uses the same simplifier without changing its operations.
All proof-only opacity is local and restored.

The explicit [StateArrow](../../theories/Instance/Set/State.v) reuses
`StateStrongM` and the general Kleisli construction, with no model-specific
Arrow law proofs or global chosen-instance registration. Temporary checks
cover both strict base/computation hom-equality orders, both strict state
carrier/equality orders, all seven basic laws, operation rewriting and
comparison. Eight transparent state computations exercise pure, first,
second, split, fanout, reversed input order, repeated transitions and nested
context reassociation. The 68 cartesian/model assumption checks and 26
monoidal-foundation checks are all closed under the global context. All
148 earlier Applicative checks were rerun successfully after extracting the
shared simplifier. No permanent tests or shared test aliases were added.
Freyd, static Arrow, ArrowApply/Choice/Loop and Day/profunctor results remain
outside this slice; batch PDF export remains with integration.

The final phase passed `dune build @all @runtest @install` with the existing
`rocq-cats` switch (Rocq/Stdlib 9.2, Dune 3.23.1). Strict bilingual HTML
export generated 276 modules per language and checked links and anchors in
557 pages; the new monoidal/cartesian/comparison explanations and State
model were inspected in both languages.

## First implementation boundary

1. Bundle a functor and its lax structure between two specified monoidal
   structures. Retain a unit map and a natural tensorator with
   associativity and both unit laws. Do not require invertibility, a
   strength, or a closed/cartesian base.
2. Prove the generic monoid transport once: `e' = F(e) ∘ φ₀` and
   `m' = F(m) ∘ φ₂`. Map homomorphisms by `fmap F` and package the functor
   between the existing monoid-object categories.
3. Check a genuinely noninvertible lax structure, independent hom/equality
   universe orders, and foundational assumptions. Keep temporary checks
   distinct from retained interface regressions.
4. Lawful Applicative, coherent operation comparison, tensorial strength and
   the ordered strong-Monad conversion, computational Arrow and its ordered
   pairing comparison above are implemented. Freyd, static-arrow and deeper
   representation results remain open in #35.

The implemented interface is
[LaxMonoidalFct MC MD](../../theories/Cat/Monoidal/Functor.v), bundling
the underlying functor through `LaxMonoidalFctToFct :> Fct C D`. Clients use
`L X` and `fmap L f`; comparison notation is `φ₀[L]` and `φ₂[L; X; Y]`
in `monoidal_scope`.
[ConstLaxMonoidalF](../../theories/Cat/Monoidal/Constant.v) supplies
a general constant example from any target monoid. Chosen identity and
constant structures are definitions that clients select explicitly.
[LaxMonoidF](../../theories/Cat/Monoidal/Transport.v) maps the existing monoid
category by `fmap L`, retaining designated equality and Type-valued witnesses.
This induced functor remains a derived construction, rather than a second
coercion from the lax structure. The broader interface survey is recorded in
[BundledInterfaces.md](BundledInterfaces.md).

The local record follow-up from `728ab7c` preserves these computational
choices through the direct `LaxMonoidalFctOfFct` constructor. Unit and
tensorator projections recover the exact supplied data. The identity unit
and tensorator compute on setoids; the existing Boolean constant examples
still demonstrate noninvertible comparisons. See the
[current record/naming checkpoint](../development/Abbreviations.md#lax-monoidal-functor-record).

The strong extension `MonoidalFct` keeps its exact lax parent and adds
Type-valued inverses. `MonoidalTensorInvN` uses the general `InvN`
construction, which derives inverse naturality. The retained identity
regressions in `Computations.v` check inherited `fmap`, the inverse unit,
and both forward and inverse tensorators by reduction. A separate temporary
audit checks constructor retention, the inverse equations and naturality,
and both strict Hom/equality orders with object universes larger than law
universes; all twelve assumption reports are closed. All twenty affected
and representative targets pass with Rocq 9.3.0, Stdlib 9.2.0 and Dune
3.23.1. This bounded checkpoint does not include a full-library build.

Retained regressions check that the Boolean-xor constant functor's unit
and tensor comparisons are not invertible, that transported operations
compute, and that transport works in both directions between categories
with `e < h < p` hom/equality levels. See
[Computations.v](../../tests/Computations.v) and
[Universes.v](../../tests/Universes.v).

[w]: https://github.com/jwiegley/category-theory/tree/99869fd8d9117e900dea862d8612033848aa01dd
[w-app]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Theory/Coq/Applicative.v
[w-app-proofs]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Theory/Coq/Applicative/Proofs.v
[w-capp]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Functor/Applicative.v
[w-lax]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Functor/Structure/Monoidal.v
[w-pure]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Functor/Structure/Monoidal/Pure.v
[w-coq]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Instance/Coq.v
[w-strong]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Monad/Strong.v
[w-kprem]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Monad/Kleisli/Premonoidal.v
[w-freyd]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Structure/Premonoidal/Freyd.v
[w-day]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Construction/Day.v
[w-coend]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Instance/Sets/Coend.v
[w-prof]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Theory/Profunctor.v
[w-prof-comp]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Construction/Profunctor/Compose.v
[w-prof-laws]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Construction/Profunctor/Laws.v
[w-cayley]: https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Construction/Cayley.v
[m]: https://github.com/leanprover-community/mathlib4/tree/9bac2d0692944a775113f7c130fd5e5b4608a854
[m-app]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/Control/Applicative.lean
[m-lax]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/CategoryTheory/Monoidal/Functor.lean
[m-mon]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/CategoryTheory/Monoidal/Mon.lean
[m-day]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/CategoryTheory/Monoidal/DayConvolution.lean
[m-day-closed]: https://github.com/leanprover-community/mathlib4/blob/9bac2d0692944a775113f7c130fd5e5b4608a854/Mathlib/CategoryTheory/Monoidal/DayConvolution/Closed.lean
[l]: https://github.com/leanprover/lean4/tree/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a
[l-lawful]: https://github.com/leanprover/lean4/blob/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a/src/Init/Control/Lawful/Basic.lean
[a]: https://github.com/agda/agda-categories/tree/ade267a5a02688fb97ec9d6e03ab6192be94439e
[a-lax]: https://github.com/agda/agda-categories/blob/ade267a5a02688fb97ec9d6e03ab6192be94439e/src/Categories/Functor/Monoidal.agda
[a-strong]: https://github.com/agda/agda-categories/blob/ade267a5a02688fb97ec9d6e03ab6192be94439e/src/Categories/Monad/Strong.agda
[a-mon]: https://github.com/agda/agda-categories/blob/ade267a5a02688fb97ec9d6e03ab6192be94439e/src/Categories/Object/Monoid.agda
[a-kl]: https://github.com/agda/agda-categories/blob/ade267a5a02688fb97ec9d6e03ab6192be94439e/src/Categories/Category/Monoidal/Construction/Kleisli.agda
[u]: https://github.com/UniMath/UniMath/tree/7a4b03cce49449f45ce0d4285615165172f50546
[u-lax]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monoidal/Functors.v
[u-strong]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monoidal/StrongMonad.v
[u-mon]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monoidal/CategoriesOfMonoids.v
[u-kl]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monads/Kleisli.v
[u-mm]: https://github.com/UniMath/UniMath/blob/7a4b03cce49449f45ce0d4285615165172f50546/UniMath/CategoryTheory/Monoidal/Examples/MonadsAsMonoidsElementary.v
[paper]: https://arxiv.org/abs/1406.4823v1

## Independent associator and unitor choices

The premonoidal migration extracts [associators](../../theories/Cat/Monoidal/Associator.v)
and [unitors](../../theories/Cat/Monoidal/Unitor.v) on the same fixed
`HasBinoidal` choice. A last-variable natural isomorphism fixes all
associator components and inverses. The general `IsNatIso` property and
`NatIsoOfComponents` view recover first- and middle-variable natural
isomorphisms on those same components. The pentagon requires no unit;
the unitor package requires no associator. `IsPremonoidal` provides the
triangle compatibility between the two choices.

`PremonoidalCat` is now a complete record with one binoidal parent.
Its constructor and parent projections provide the inheritance conversions;
no forwarding conversion function or extra coercion is introduced.
[Bifunctor assembly](../../theories/Cat/Monoidal/Bifct.v) and
[Arrow computations](../../theories/Cat/Computational/Arrow/Premonoidal.v)
construct the two packages independently and combine their original
selected maps. Monoidal and symmetric clients retain their parameterized
interfaces while selecting one tensor and its indexed extension.

The retained interface checks reject automatic selection of unitors from
an associator alone, or an associator from unitors alone. Concrete Boolean
regressions compute a middle-variable inverse and a bundled unitor inverse
by reflexivity. A temporary audit checks conversion of the three
associator views, actual category and instance coercions, explicit choice
isolation on one category, and strict levels `h < p < l < o` in both
Hom/equality orders. All 23 assumption reports are closed, including the
new builders and Freyd context unit/associativity clients. Native equality
appears only in temporary conversion checks and concrete regression values;
the mathematical interfaces continue to use specified Hom equality.

The stable checkpoint builds all 617 library modules and
`tests/Interfaces.vo`, `tests/Computations.vo`, `tests/Universes.vo` with
Rocq 9.3.0, Stdlib 9.2.0 and Dune 3.23.1 in the `rocq-cats` switch.
The incremental command `dune build -j2 theories tests/Interfaces.vo
tests/Computations.vo tests/Universes.vo` takes 340.141 seconds on this
worktree. This includes cached dependencies; it is not a clean-build
benchmark. Sources remain unchanged during validation. No HTML/PDF export,
install check or full test alias is included. The audit is temporary;
interface and computation regressions remain in the repository.

## Binoidal record and fixed-map laws

The binoidal checkpoint separated the complete `BinoidalCat` record
from the chosen `HasBinoidal C` extension. Left and right actions share one
object tensor. Each has an `IsFct` witness on its fixed maps, reusing
[Cat.Functor.Core](../../theories/Cat/Functor/Core.v). `MakeFct` supplies the
ordinary context functors transparently. Respectfulness remains required:
identity and composition preservation do not by themselves ensure that an
operation descends to the specified hom equality.

`BifctHasBinoidal` and `ArrowHasBinoidal` retain the original maps and
proofs, grouped by context side. Their complete bundles store the same
category and evidence. At that checkpoint the parameterized premonoidal
layer read that same choice through `PremonoidalToHasBinoidal` and its
transparent `PremonoidalToBinoidalCat` view; the following premonoidal
migration replaces that interim view with a stored parent projection. No interchange, symmetry, unit, associator,
function equality or proof irrelevance is added to the binoidal interface.
The retained Boolean computations distinguish the two actions using a
nonidentity map; import regression checks keep model selection explicit.

The binoidal checkpoint built all 613 library modules and the three
representative regression targets. Twenty temporary assumption reports are
closed, including strict size, conversion, same-category choice isolation
and computational-map checks. No additional global assumptions are used.
The `day_monoid_mul_roundtrip` proof pins the tensor, participating functors
and existing Day choice when applying `day_extend_proper`; inference through
reconstructed bundles otherwise unfolds large structures. In a temporary
statement-timing audit, that explicit application takes about 0.002 seconds.
The theorem's assumptions, conclusion and computational constructions stay
the same; no opacity is introduced.

## Proof transparency in the functor and tensor migration

The [#47 audit](https://github.com/Godalin/rocq-cats/issues/47) closes
proof-only respectfulness, functoriality, naturality, and coherence with
`Qed`. The programs still expose their maps and structural projections.
In particular, the component-construction obligations for
`BifctTensorN` and `DayAssociatorFctN` use `Defined`, while their
naturality obligations use `Qed`. The temporary constructor and
semigroupal probes check definitional equality of data projections,
instance search, independent universes and assumptions.

The identity law of [`FctPsh`](../../theories/Instance/Set/Functor.v)
is a computational exception. Its lifted natural isomorphism has an inverse
component that `nerve_identity_inverse_computes` projects and reduces.
The probe-presheaf comparison obligations retain `Defined`.

With Rocq 9.3.0, Stdlib 9.2.0 and Dune 3.23.1, we compiled each module
three times in each of two temporary source snapshots, alternating the
order. Both snapshots include the removal of the `IdF` and `CompF`
canonical registrations. Dune built the dependencies beforehand. The
table gives median compiler CPU time in seconds for a single module with
its dependencies already built. Other compilation was running, so
elapsed time is excluded from the comparison. These measurements cover
selected modules with warm dependencies.

| Module | Before | After |
| --- | ---: | ---: |
| `Cat.Functor.Product` | 1.57 | 1.54 |
| `Cat.Day.Universal` | 11.33 | 10.90 |
| `Cat.Day.Map` | 14.22 | 7.38 |

A temporary `Program` example under `Local Unset Transparent Obligations`
made both an automatically solved law and an automatically solved data
obligation opaque. The latter blocked reduction of its projection to a
numeral. Providing the data explicitly recovered the reduction. The
library uses explicit endings for the reviewed obligations.

## Two-sided context and centrality prerequisite

The user-approved serial slice starts from `751de86` on `monoidal-cat-view`.
The existing generic Arrow has a left-context action over a named monoidal
base; that alone does not specify a right-context action. This slice
extracts [BinoidalCat](../../theories/Cat/Monoidal/Binoidal.v): one object tensor
and two separately functorial arrow actions, without units, associators,
symmetry or effect interchange. Derived fixed-context functors share that
same object tensor. Public `binoidal_scope` notation writes the tensor as
`X ⊗ Y`, left context as `Z ⊲ f`, and right context as `f ⊳ Z`.

[Centrality](../../theories/Cat/Monoidal/Center.v) is a Type-valued predicate
on an arrow: it supplies exchange with every partner, in either tensor
position. Specified-equal arrows share centrality, and central arrows are
closed under identity and composition. Ordered sequencing agrees with the
opposite execution order when either factor is central. There is no
principle asserting this for two arbitrary effects.

[MonoidalBinoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Binoidal.v) explicitly adapts
an existing monoidal tensor, with all arrows central by bifunctoriality.
It is not another coercion or globally chosen parent of MonoidalCat.
[ArrowBinoidal](../../theories/Cat/Computational/Arrow/Binoidal.v) reuses
`ComputationCat A`, the selected value products and existing `first`/`second`
operations. `ArrowPureF` is identity on the shared value-object type and
reuses the original pure-arrow action. Both old context-naturality laws
prove that every pure arrow is central. Generic ordered sequencing agrees
with the existing Arrow split. No concrete model laws are reproved.

The adapter fixes the value-category product explicitly even though value
and computation objects have the same type. Right-context action currently
uses the existing cartesian exchange. The general binoidal foundation
requires no symmetry, but extending the one-sided generic Arrow to two
sides over a weaker base needs extra data or a coherent exchange structure.
At this checkpoint, full premonoidal structural isomorphisms and coherence,
symmetric structure, and the complete Freyd characterization were still
later tasks. The next slice below supplies the general premonoidal layer.
The pinned [Wiegley binoidal interface](https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Structure/Binoidal.v)
was rechecked alongside the cached premonoidal/Freyd sources; the existing
prior-art and compatibility boundaries above still apply.

Validation used the existing `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed. All 73 temporary `Print Assumptions` checks reported
`Closed under the global context`: both strict hom/equality universe
orders, independent value/computation hom equalities, centrality rewriting,
explicit model choices, both State carrier/equality orders and concrete
pure/context/sequence reductions were checked. The State example proves
that changing state before reading differs from reading before changing,
and that the changing computation is not central. These are temporary
checks, with no permanent test or shared test configuration changes.

Strict bilingual HTML generated 287 modules per language and checked
links/anchors in 579 pages. All four new interface/adapter pages were
inspected in both languages. Batch PDF export and updating `typeprop`
remain with the integration session. The delivered foundation is ready
for independent integration before further premonoidal/Freyd work.

## Premonoidal structure prerequisite

This user-approved serial slice starts from `3fc3ffb` on `monoidal-cat-view`.
[PremonoidalCat](../../theories/Cat/Monoidal/Premonoidal.v) inherits one binoidal
structure through `PremonoidalB :> BinoidalCat C`, with the same projection
registered for instance search. It adds a chosen unit, central associator
and unitors, their separate naturality, and pentagon/triangle coherence.
Carrier, hom and equality sizes remain independent; all equality and
centrality witnesses remain Type-valued. No structural operations or
underlying category are selected a second time.

The general [inverse-square lemma](../../theories/Cat/Isomorphism.v) inverts
the vertical isomorphisms of any commuting square using specified hom
equality. [Centrality of an inverse](../../theories/Cat/Monoidal/Center.v)
uses that lemma with the fixed-context functors. The
[associator](../../theories/Cat/Monoidal/Associator.v) and [unitor inverse laws](../../theories/Cat/Monoidal/Unitor.v) derive all
three inverse centrality witnesses and all five inverse naturality
squares. Forward and inverse maps are projections of the same selected
isomorphisms; inverse centrality/naturality are not duplicate class fields.
Public `premonoidal_scope` notation exposes the unit and both directions
of each structural map; object tensor and contexts retain binoidal notation.

[MonoidalPremonoidal](https://github.com/Godalin/rocq-cats/blob/0a41be9/theories/Cat/Monoidal/Premonoidal.v) is an explicit
client of the new layer. It reuses `MonoidalBinoidal`, the original unit,
associator/unitors and their inverse components. Separate naturality
specializes existing joint naturality; existing coherence is reused.
The old `MonoidalCat` interface and all concrete model constructors remain
available in their existing form. Migrating its parent and deriving the
bifunctor from interchange is a later bounded task. Constructing the
computational Arrow premonoidal structure, symmetric/Freyd interfaces and
the full characterization also remain open. No concrete model laws are
reproved here.

Validation uses the existing `rocq-cats` switch: Rocq/Stdlib 9.2.0,
OCaml 5.3.0 and Dune 3.23.1. Full `dune build @all @runtest @install`
passed. All 63 new temporary `Print Assumptions` probes and all 73 repeated
binoidal/Arrow probes reported `Closed under the global context`.
The new probes check the inherited coercion/instance chain, both strict
hom/equality universe orders, multiple explicit structures on one category,
absence of globally selected models, transparent forward/inverse
associator/unitor reductions, and inverse centrality of a nonidentity
isomorphism. The prior State order counterexample and its noncentral
effect remain valid. These checks are temporary; no permanent tests or
shared test configuration were changed.

Strict bilingual HTML generated 290 modules per language and checked
links/anchors in 585 pages. All three new pages were inspected in both
languages, together with the added general-lemma anchors. The structural
inventory covers all 91 interfaces exactly once (64 classes, 27 records).
Batch PDF export and `typeprop` integration remain with the integration
session; this foundation can be integrated independently.

## Monoidal parent migration

This user-authorized serial slice starts from `0a41be9` on
`monoidal-cat-view`. [MonoidalCat](../../theories/Cat/Monoidal/Monoidal.v) now
inherits one `PremonoidalCat C` through `MonoidalP :>`, exported as the
inherited instance. A single interchange equation supplies centrality
for every arrow; the other centrality square is obtained by swapping
arguments. The stored tensor bifunctor and direct category bypass are
removed. The derived tensor functor sequences the inherited actions,
while unit, associator/unitors, inverse components and coherence come
from the same parent.

Two proofs use weaker hypotheses than monoidal structure:
[central_sequence_comp](../../theories/Cat/Monoidal/Center.v) needs centrality
only of the crossing arrow, and
[tensor_assoc_sequence_natural](../../theories/Cat/Monoidal/Associator.v)
uses only separate premonoidal naturality. The monoidal tensor functor
and joint associator naturality reuse these proofs. Derived natural
isomorphisms retain the original inverse components rather than storing
new choices.

[BifctBinoidal](../../theories/Cat/Monoidal/Bifct.v) extracts separate
actions from any tensor bifunctor. The
[BifctMonoidal](../../theories/Cat/Monoidal/Bifct.v) assembly constructor
then reuses supplied natural structural isomorphisms and two coherence
proofs. It supplies a natural isomorphism between its derived tensor and
the original bifunctor, with identity components. The two concrete model
families (cartesian and bicategory endomorphism, hence endofunctors) use
this shared constructor; there is no staging data record or equality of
functor/law records. The transitional `MonoidalBinoidal` and
`MonoidalPremonoidal` adapters from earlier milestones are removed in
favor of the inherited projections.

Cartesian and endomorphism comparison laws adapt weaker clients using
specified equality. [Cartesian binary lifting](../../theories/Cat/Monoidal/Cartesian.v)
transports generic lax lifting results without adding pure maps,
exponentials or strength. Applicative, Monad, strength and Arrow clients
use these comparisons; tensorator natural transformations have the same
derived tensor functor at their endpoints. Monad–monoid functors keep
the underlying arrow and transport its Type-valued preservation witness.
At this milestone computational Arrows had only their binoidal structure;
no interchange for arbitrary State effects was inferred. The following
batch supplies their premonoidal structure; symmetric/Freyd structure and
translations remain open.

Validation used the existing `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed, including the unchanged interface, universe and computation tests.
All 212 temporary `Print Assumptions` checks were closed under the global
context: 76 new monoidal-parent checks and 136 adapted premonoidal/binoidal
checks. They cover both strict hom/equality universe orders, the full
inherited coercion/instance chain, reconstruction of existing monoidal
structures and tensor natural-isomorphism comparison, explicit model
selection, transparent tensor/structure/inverse reductions and the
unchanged State order counterexample. No permanent tests or shared test
configuration were changed. The existing `AGENTS.md` learning section now
records the comparison and tensorator-endpoint discipline.

Strict bilingual HTML generated 291 modules per language and checked
links/anchors in 587 pages. The monoidal core, all three new modules and
the added premonoidal sequence law were inspected in both languages.
The inventory still covers all 91 interfaces exactly once (64 classes,
27 records), with all 29 `Has*` classes retained. Batch PDF export and
`typeprop` integration remain with the integration session.

## Computational Arrow premonoidal structure

This user-authorized serial batch starts from `1b341ec` on
`monoidal-cat-view`. [ArrowPremonoidal](../../theories/Cat/Computational/Arrow/Premonoidal.v)
constructs a `PremonoidalCat (ComputationCat A)` for a computational Arrow
over the cartesian monoidal structure supplied by named terminal and
product choices. Its parent is exactly the existing `ArrowBinoidal A`:
the object tensor, equality and both context operations are inherited,
without new choices or a direct ancestor bypass.

The associator and both unitors, including their inverse maps, are pure
images of the same selected value isomorphisms through `ArrowPureF A`.
The existing `fct_is_iso` theorem supplies the inverse equations;
`arrow_pure_central` supplies all three centrality witnesses. Unit
naturality reuses the two projection laws. The associator's left/right
naturality reuses `arrow_first_assoc` and `arrow_context_assoc`; the new
[arrow_middle_assoc](../../theories/Cat/Computational/Arrow/Cartesian.v)
proves middle naturality from nested left contexts and ordinary context
exchange. It never exchanges two effectful computations. Pentagon and
triangle are the functorial images of existing value coherence, without
reproving product coherence or individual model laws. All inverse
centrality and naturality laws then follow from the general premonoidal
theory, with no duplicate structure fields.

The construction is explicitly selected and requires neither exponentials
nor commutativity. It applies directly to the existing pure and strong
Monad/Kleisli Arrow models, including State. This batch does not supply a
general noncartesian right action, symmetric/Freyd interfaces or an
Arrow–Freyd equivalence; those are subsequent tasks. In particular,
the unchanged Boolean-state toggle/read example still distinguishes
execution order and supplies a noncentral computation in this very
premonoidal structure.

Validation used the unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed. All 79 temporary `Print Assumptions` checks were closed under
the global context. These checks cover both strict hom/equality universe
orders, separately sized value/computation object and hom universes,
the exact inherited parent and its instance search, pure preservation of
both associator directions, both strict state carrier/equality orders,
transparent structural maps/inverses and the original observable-order
and noncentrality counterexamples. Concrete clients specify the computation
category explicitly where value and computation objects share a type;
object arguments alone do not determine the ambient hom-set.

Strict bilingual HTML generated 292 modules per language and checked
589 pages. The new module, middle-context lemma, both language texts and
public symbol anchors were inspected. The inventory still covers all
91 class/record interfaces exactly once (64 classes, 27 records), with
all 29 `Has*` classes retained. No permanent tests or shared test
configuration were added or changed. This task-branch foundation is ready
for independent integration; `typeprop` and batch PDF export remain with
the integration session.

## Symmetric contexts and Freyd foundation

This user-authorized serial batch starts from `4098284` on
`monoidal-cat-view`. The classical conditions were rechecked against
[Jacobs–Heunen–Hasuo, definitions 6.2–6.4](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/35C603B99F43CBD8109C97FA51BDAB23/S0956796809007308a.pdf/categorical_semantics_for_arrows.pdf)
and [Selinger, section 2.1](https://www.mscs.dal.ca/~selinger/papers/control.pdf).
The interface includes finite-product values, symmetric premonoidal
computations, a central identity-on-objects inclusion and strict
preservation. It does not use the weaker third-party effectful interface
as a substitute for these requirements.

[SymPremonoidalCat](../../theories/Cat/Monoidal/Symmetric.v)
inherits one premonoidal parent through Minks. `HasTensorSym` stores
central exchange, involution and left-variable naturality. Two further
mixins relate the same exchange to the associator and unitors by the
hexagon and unit equations.
The symmetry isomorphism uses the opposite exchange as its transparent
inverse; right-variable naturality follows by inverting the first square.
A derived conjugation law recovers right action from left action.
[CartSymPremonoidal](../../theories/Cat/Monoidal/Cartesian.v)
inherits the existing cartesian monoidal parent's premonoidal structure,
proving only the new exchange equations from products.

[ArrowSymPremonoidal](../../theories/Cat/Computational/Arrow/Symmetric.v)
retains exactly `ArrowPremonoidal A`. Exchange is pure product exchange,
central by `arrow_pure_central`. Its naturality follows from the existing
right-context definition and involutive pure exchange. Hexagon and unit
coherence are functorial images of the generic cartesian symmetry laws;
no separate Reader or State coherence proofs are added. Symmetry exchanges
context positions without exchanging the execution of two effects.

[ArrowSymPremonoidal](../../theories/Cat/Computational/Arrow/Symmetric.v)

[FreydCat](../../theories/Cat/Computational/Freyd/Core.v) bundles the pure
ambient functor with chosen cartesian values and symmetric premonoidal
computations. Its actual computation category is the existing induced
category indexed by value objects. `FreydPureF` therefore has identity
object map by construction; arbitrary unused ambient objects are not
claimed to belong to this Freyd category. The reusable
[InducedF](../../theories/Cat/Induced.v) supplies this factorization and now
also supplies the existing `ArrowPureF`, keeping its arrow/object maps.
No equality of object-map functions or bijection of ambient object types
is required.

Strict object preservation retains explicit tensor/unit equality
witnesses. The existing `eq_to_hom` operation supplies every boundary
transport. Context preservation, both unitors, both nested associator
boundaries and symmetry use those same witnesses coherently, and every
arrow equation uses specified Hom equality. There is no UIP, function
extensionality, proof irrelevance or identification of law records.
[ArrowFreyd](../../theories/Cat/Computational/Arrow/Freyd.v) reuses the
same pure functor, finite-product choices and symmetric computation
parent. All its object equalities are reflexive, so boundary transports
compute to identities; preservation reuses the existing Arrow laws.

This delivers the symmetric/Freyd interfaces and the forward
computational Arrow-to-Freyd construction. Reverse translation, explicit
round-trip comparisons and their precise categorical equivalence level
remain open. No full Arrow/Freyd correspondence, ordinary-arrow-category
change, closed Freyd/ArrowApply result or general noncartesian right
action is claimed. All model structures remain explicitly selected.

Validation used the unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed. All 169 temporary assumption checks were closed under the global
context: 90 new symmetric/Freyd checks and the 79 premonoidal checks rerun
after extracting `InducedF`. They cover both strict hom/equality universe
orders, separately sized value/computation objects and hom-sets, both
strict state carrier/equality orders, inherited coercions/instances,
identity-on-objects inclusion, exact shared structure choices, transparent
exchange/inverse/boundary computations, structural preservation and the
unchanged State order/noncentrality counterexamples. Imports do not select
a default symmetric or Freyd model. No permanent tests or shared test
configuration were changed.

Strict bilingual HTML generated 297 modules per language and checked
599 pages. All five new module texts, interface-field anchors and the
shared `InducedF` documentation were inspected in both languages. The
inventory covers all 93 interfaces exactly once (66 classes, 27 records),
retaining all 29 `Has*` classes. The existing `AGENTS.md` learning section
records object-indexed inclusions, explicit ambient-category inference and
consistent boundary witnesses. This foundation is ready for independent
integration before the reverse translation; `typeprop` and batch PDFs
remain with integration.

## Freyd reconstruction and round trips

This slice continues the symmetric/Freyd foundation on `monoidal-cat-view`
from `af3d0fe`. It delivers the reverse translation and explicit round-trip
comparisons deferred by that slice. Ordinary arrow categories, self
enrichment and concrete model definitions are unchanged.

The reusable [functor transport](../../theories/Cat/Functor/Transport.v)
changes object representatives along chosen isomorphisms and supplies a
natural isomorphism to the original functor. Its boundary-naturality lemma
uses the weakest sufficient assumptions: a natural incoming boundary and
an invertible outgoing one. General
[tensor transport](../../theories/Cat/Monoidal/Center.v) uses context
functors and centrality of transported identities. Premonoidal associators
and the left unitor now expose the natural transformations used by this
argument. Equality isomorphisms, commuting-square composition and the
natural-isomorphism comparison for induced factorization live with their
general category theories.

[Freyd contexts](../../theories/Cat/Computational/Freyd/Context.v) conjugate
the original left action by exactly the tensor boundaries supplied by the
Freyd structure. Fixed and nested boundaries form natural transformations
and natural isomorphisms. Naturality across these boundaries derives the
value-unit and value-associativity equations without identifying equality
witnesses. [FreydArrow](../../theories/Cat/Computational/Freyd/Arrow.v)
therefore reconstructs the computational Arrow from the same selected
cartesian values and pure inclusion. Computational witnesses, conjugating
inverse maps and model reductions remain transparent.

The [round-trip module](../../theories/Cat/Computational/Freyd/RoundTrip.v)
compares Arrow pure maps and contexts in specified Hom equality and the
pure functors by natural isomorphism. On the Freyd side it supplies an
actual categorical equivalence in the existing `CatCat` interface between
the original and returned value-indexed computation categories. Its pure
inclusions are naturally isomorphic, and its comparison preserves left
and right actions, both unitors, associator and symmetry across the
original selected boundaries. The right-action comparison composes the
exchange and left-action boundary squares; it assumes no effect
interchange.

These are comparisons of supplied structures at the actual computation
categories. They do not assert an equivalence with unused ambient objects,
native equality of functor/law records, an equivalence of 2-categories of
structured functors, or soundness/completeness for an Arrow syntax. Closed
Freyd/ArrowApply and the separate static-Arrow characterization remain
future work. No extra axiom, UIP, proof irrelevance or function
extensionality is introduced. Model choices remain explicit.

Validation used the unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed. All 278 temporary `Print Assumptions` checks were closed under the
global context: the previous 169 checks, 51 general constructions/laws,
and 58 new universe/concrete probes. The new probes cover both strict
hom/equality universe orders, separately sized value/computation categories,
both strict state carrier/equality orders, returned pure/context operations,
inverse comparison components and both equivalence functors. Returned State
sequencing still computes different results in the two execution orders;
the original noncentrality and order counterexamples were rerun. No
permanent tests or shared test configuration were changed.

Strict bilingual HTML generated 302 modules per language and checked
609 pages. Both languages were inspected for the five new modules and
five extended foundational modules, including public anchors. The
inventory covers all 93 interfaces once (66 classes, 27 records), with all
29 `Has*` classes retained. The existing `AGENTS.md` learnings record
explicit category arguments and transport of naturality across coherent
boundaries. This task branch is ready for integration; `typeprop` and
batch PDF exports remain with the integration session.

## Static Arrow construction

This slice continues E of #35 from `b86fee1` on `monoidal-cat-view`.
[StaticCat and StaticArrow](../../theories/Cat/Computational/Arrow/Static.v)
construct static computations from the existing Applicative on a category
with selected terminal object, products and exponentials. The hom-set from
one value object to another is the base hom-set of global elements of the
Applicative image of their internal function object. Its specified,
Type-valued equality is reused directly. Effects are combined before the
resulting function receives its value argument; the value argument cannot
select a different effectful computation.

The construction first extracts two general components.
[Exponential context theory](../../theories/Cat/Exponential/Context.v) names
ordinary functions, presents the existing internal composition in execution
order, and derives internal product-context diagrams by evaluation and
exponential extensionality. [Contextual binary lifting](../../theories/Cat/Applicative/Lifting.v)
specializes the existing lax postcomposition, input naturality, pure-input
and associativity laws by pairing contextual inputs. Its incoming product
boundaries are pinned to the same chosen products. Temporary proof opacity
is restored before exposing clients; computational maps stay transparent.

Static composition lifts internal sequencing with the first computation
before the second. Pure inclusion names the base arrow and applies pure;
context extension maps the ordinary internal context function through the
same Applicative. The full computational Arrow laws follow from these
general diagrams. No strength, Monad, commutative tensorator, well-pointedness
or native equality of functions or law records is assumed. The existing
Freyd construction and round-trip comparison consume this Arrow unchanged.
This delivers a structural static representation, not a completeness or
equivalence theorem for a typed static-arrow calculus. ArrowApply, the
static/dynamic syntax comparison and Day/strong-profunctor results remain
open.

The new strict-level probes exposed an existing restriction in
[Reader](../../theories/Instance/Set/Reader.v): its helpers and upper packaging
had identified the environment's universes with ambient ones, despite the
underlying `ReaderF` keeping them independent. Separate helper parameters
and explicit levels on the tensorator, pure transformation, lax structure
and `ReaderA` repair that restriction. The reader operations and witnesses
are unchanged. Strict probes now check both environment carrier/equality
orders, with ambient carrier strictly above ambient equality, independently
of the static closed client. Concrete static Reader/State probes use the
existing closed setoid model's common ambient carrier/equality level;
no resizing or stronger closed-setoid model is claimed.

Validation used the unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1). Full `dune build @all @runtest @install`
passed after the Reader repair. All 251 temporary assumption checks were
closed under the global context: 91 static/general construction and client
checks, 12 Reader signature checks and 148 rerun Applicative/strong-Monad
checks. They cover both strict hom/equality orders, objects strictly larger
than both, separate environment and ambient levels, explicit model enabling,
pure/context/first computations, noncommuting State execution orders and
Freyd round-trip computations and comparison inverses. No permanent tests
or shared test configuration were changed.

Strict bilingual HTML generated 305 modules per language and checked
615 pages. The three new modules and the updated Reader documentation
were inspected in both languages, including public anchors. The complete
inventory still covers 93 interfaces exactly once (66 classes, 27 records)
and all 29 `Has*` classes. The existing `AGENTS.md` learnings now record
chosen product boundaries for contextual lifting proofs. The branch is
ready for integration; `typeprop` and batch PDF export remain with the
integration session.

## Section openings after the integrated baseline

The task branch was rebased onto integrated baseline
`fee98fcff6c656d4dae26425401db7a2bc403b9b`; the static construction is now
`a167f6c` (formerly `a454875`). The only conflict was in `AGENTS.md` and
retained both upstream Section requirements and the existing field/comment
spacing rule. All task-modified source Sections now have an adjacent
bilingual mathematical opening. Twenty missing openings were added, and
seven existing entrance descriptions were clarified. Removing comments
leaves every source token unchanged in this documentation batch.

With the unchanged `rocq-cats` switch, full `dune build @all @runtest
@install` passed. All 251 static/Reader/Applicative temporary assumption
checks were rerun successfully. Strict bilingual HTML generated 329 modules
per language, checked 663 pages, and all 54 changed English/Chinese comment
blocks were checked in their language's output. The declaration inventory
now includes the four upstream interfaces and covers all 97 declarations
once (68 classes, 29 records), retaining 29 `Has*` classes. No permanent
tests, shared environment or integration branch were changed. Batch PDF
exports remain with the integration session.

## Static values and ordered Applicative operations

Following the Section documentation commit `d3798ae`, this phase adds
[Static values](../../theories/Cat/Computational/Arrow/Static.v) on the
same integrated baseline `fee98fcff6c656d4dae26425401db7a2bc403b9b`.
Transparent evaluation and abstraction compare terminal-input static
computations with global Applicative values; the underlying maps also
commute with every external-context substitution. Both inverse laws,
respectfulness and equality reflection use only the original hom equality.
The comparison reuses the exponential-unit isomorphism, without equality
of function/law records or a well-pointedness assumption.

Pure values, ordinary result mapping and ordered application are preserved
and reflected. Arbitrary binary lifting is represented by a static
composition which first abstracts the left value, then composes with the
function produced from the right value. This retains the left-before-right
effect order. Three ordinary diagrams were extracted to
[exponential context theory](../../theories/Cat/Exponential/Context.v): terminal
evaluation of names and sequencing, and binary application. The binary
diagram needs no terminal object or effect structure. All lifting proofs
reuse the general shared-context Applicative laws.

The unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0,
Dune 3.23.1) passed full `dune build @all @runtest @install`. All 91 new
temporary assumption checks are closed under the global context: 20 public
definitions/laws, 51 signatures instantiated with both strict hom/equality
orders and objects strictly above hom/equality, and 20 concrete definitions
and reductions. The concrete checks include explicit model enabling,
Reader computations, both State inverse reductions, pure/state retention,
and ordered binary State outputs `(false, true)` versus reversed
`(false, false)` from the same initial state. These supplement the 529
successful rebase checks (91 static, 278 Freyd, 148 Applicative/strong Monad,
12 Reader signatures); no permanent tests were added.

Strict bilingual HTML generated 330 modules per language and checked
665 pages. All 78 English/Chinese comment blocks and all public anchors
in the two affected modules were checked in their language's output.
The inventory covers all 97 interfaces exactly once (68 classes, 29 records)
and retains all 29 `Has*` classes. The latest fetched integration baseline
is still `fee98fc`; only the task branch is updated. Batch PDF export remains
with integration. A direct comparison with derived Arrow fanout, typed
syntax preservation/reflection, and static/dynamic representation conditions
remain future work; this phase proves operations on actual arrows rather
than a syntactic equational equivalence.

## Static cartesian operation comparisons

On task branch `monoidal-cat-view`, following `1f2450c` and based on the
unchanged integrated baseline `fee98fcff6c656d4dae26425401db7a2bc403b9b`,
[Static cartesian operations](../../theories/Cat/Computational/Arrow/Static.v)
compares actual derived first, ordered split and fanout with Applicative
lifting. For every ordinary input object, fanout lifts the existing inverse
product-exponential comparison. Split precomposes the two internal
functions with their respective input projections. Right context is
conjugated from the original left context by pure exchange, without
selecting another action.

The ordinary diagrams are reusable in
[exponential context theory](../../theories/Cat/Exponential/Context.v).
[Exponential laws](../../theories/Cat/Exponential/Laws.v) now expose contextual
application of the product comparison and its coherence with terminal
argument evaluation. These reuse the existing inverse transpose formula,
not a second universal-property proof. Products and exponentials suffice
for the context diagrams; terminal evaluation additionally uses the chosen
terminal object. Applicative lifting uses the existing contextual laws.

At terminal input, the transparent value comparison preserves ordered
pairing and every binary lifting expressed as fanout followed by a pure
binary operation. Its inverse reflects those same operations. All
comparisons use HomEq and retain left-before-right effects, without
commutativity, strength or Monad assumptions. The work remains categorical
semantics; following the user's priority, typed syntax is deferred until
the semantic structures and their correspondence conditions are established.

The unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0,
Dune 3.23.1) passed full `dune build @all @runtest @install`. All 284
temporary assumption checks were closed under the global context: 102 new
checks, 91 existing value-comparison checks and 91 static-Arrow/Freyd client
checks. The new batch covers all 13 public definitions/laws, 52 strict
signatures (both hom/equality orders with objects strictly below or above
both), four Reader/State environment-level signatures and 33 concrete
constructions/reductions. Concrete checks include actual first/split/fanout,
State execution-order differences, both value comparison directions,
Reader evaluation and a binary operation discarding its left result while
retaining that computation's observable state effect. No permanent tests
or shared test configuration changed.

Strict bilingual HTML generated 331 modules per language and checked
667 pages. All 104 bilingual comment blocks and 98 public anchors in the
three affected modules were checked against their generated language
outputs, including generated anchors for Unicode names. The inventory
still covers all 97 class/record declarations exactly once, including all
29 `Has*` classes. Only this task branch is updated; `typeprop`, the shared
toolchain and batch PDF export remain with integration. The remaining
semantic work concerns reconstruction and precise static/dynamic or
ArrowApply conditions, without treating syntax as the next required phase.

## Revalidation on the advanced integration baseline

The final handoff check found that local `typeprop` had advanced to
`89580d6ee75110d30fc4a82d6c60fb44f28aabc1`, while the fetched remote still
reported `fee98fc`. The task branch was rebased without conflicts onto that
local integrated baseline. The fanout mathematics is now `3c971d7`
(formerly `bc077f1`); all three affected theory modules are byte-identical
to their pre-rebase versions. This updates the preceding handoff baseline
without extending the mathematical scope or changing the integration branch.

On `89580d6`, full `dune build @all @runtest @install` and all 284 temporary
assumption checks were rerun successfully (102 new interfaces/clients,
91 value comparisons, 91 static-Arrow/Freyd checks). Strict bilingual HTML
now covers 336 modules per language and checks 677 pages, including the
five modules added by integration. The same 104 bilingual comment blocks
and 98 public anchors were checked again; the exact inventory remains
97 interfaces. The unchanged project switch and explicit model selection
were retained. Batch PDFs remain with integration; syntax remains deferred.

## Global-computation foundations

Following `4cd858a`, the #35 task independently adds the general ordered
pairing laws, the terminal-input Hom lax functor and constant respectful
maps. The existing Hom functor supplies functoriality, and `comp_square`
composes the three associativity naturality squares. Neither a monad nor
closedness nor interchange of two effects is required. The result lands
in setoids, keeping the computation category's native hom/equality levels;
it is not automatically an endofunctor on an arbitrary value category.

Targeted Global/Constant builds passed in the unchanged `rocq-cats` switch.
All 22 temporary assumption checks are closed under the global context:
all 16 public declarations and six independent-universe probes. These
separate the two categories' hom/equality levels in both strict orders
and keep constant-map source and target levels distinct. There are 339
modules and the same 97 interfaces. No permanent test or shared toolchain
was changed. Setoid-base Applicative packaging and static reconstruction
are the dependent next slice of this same authorized task; syntax stays
paused until the semantic development is established.

## Arrow values and static Applicative recovery

This slice continues on `monoidal-cat-view` from the validated integrated
baseline `89580d6ee75110d30fc4a82d6c60fb44f28aabc1`. The reusable
terminal-input Hom/lax foundation was delivered independently in
[078ba8f](https://github.com/Godalin/rocq-cats/commit/078ba8fe97f04fdc885579b3a44bd3a4af32e465).
[The setoid adapter](../../theories/Instance/Set/Arrow.v) supplies `ArrowA`
using that same lax structure and pure constant arrows. Computation hom
carrier/equality levels match the ambient setoid levels; computation
objects retain an independent universe. No Monad, strength or exponentials
are required by this adapter. Imports enable no chosen model structure.

[Static recovery](../../theories/Instance/Set/StaticArrow.v) works in the
existing closed setoid model at a common carrier/equality level. It reuses
two exponential-unit isomorphisms to compare the recovered and original
Applicatives by a transparent natural isomorphism. Both transformations
preserve pure values, ordered pairing and every ordinary binary lifting.
This establishes the Applicative-to-static-Arrow-to-Applicative round trip
on that model, without equating functor or law records. It does not
reconstruct arbitrary dynamic Arrows. General static/dynamic reconstruction
conditions and the ArrowApply/Monad relationship remain subsequent semantic
work; typed syntax stays deferred.

Full-library `dune build @all @runtest @install` passed with the unchanged
`rocq-cats` switch: Rocq/Stdlib 9.2.0, OCaml 5.3.0 and Dune 3.23.1.
All 95 comprehensive temporary assumption checks were closed under the
global context: all 33 public declarations across the five new modules,
26 universe probes and 36 concrete constructions/reductions. The probes
separate the two abstract categories' hom/equality levels, vary the setoid
adapter's carrier/equality order and computation-object level, and separate
Reader/State environment sizes below the existing closed-model bound.
Concrete checks cover pure values, both inverse equations, pairing, binary
lifting, ordinary State Arrow values, left-before-right State effects and
Reader recovery. Model-import probes also check explicit structure enabling.
The earlier 22 foundation checks overlap this comprehensive batch and are
not counted as additional distinct checks.

Strict bilingual HTML generated 341 modules per language and checked local
links and anchors in all 687 pages. All 76 bilingual documentation blocks
and 66 public declaration anchors across the five new modules were checked
in the appropriate reading edition. The inventory remains 97 interfaces
(68 classes, 29 records), including 29 `Has*` classes. Abstract pointwise
inverse lemmas avoid normalizing large lifted computations; computational
maps remain transparent, and the existing `AGENTS.md` learning records this
proof technique. No permanent tests, shared test aliases, shared toolchain
or `typeprop` updates were introduced. Batch PDF export remains with the
integration session.

## Inferred universe instances in computational models

Following the user's readability request, the Reader tensorator, State
multiplication/strength transformations and setoid Arrow adapter omit
seven repeated universe instances. Each still fixes its necessary size
boundary once; functor composition, product functors and transformation
endpoints infer the other occurrences. General Monad, Applicative and
computational Arrow theory already uses inferred instances. The remaining
model annotations preserve independent environment, ambient carrier and
equality levels, or state the existing closed-model common-level bound.
No mathematical interface, operation or universe binder order is changed.

The unchanged `rocq-cats` switch passed full-library
`dune build @all @runtest @install`. Twenty-eight temporary probes check all
Reader/State functor, natural transformation and chosen computational
structures with both strict environment carrier/equality orders below
independent ambient levels. The existing 95 Arrow-value/static-recovery
checks were rerun, including their four independent adapter-level orders
and transparent Reader/State computations. All 123 assumption reports are
closed under the global context. A separate temporary probe against the
committed Reader source confirms that the function-setoid size bound is
pre-existing, rather than introduced by this simplification. Strict
bilingual HTML again covers 341 modules per language and 687 checked pages.
No permanent test, interface, chosen instance, shared toolchain or
integration-branch update was added.

## Global-computation context foundation

The static-interpretation slice rebases `monoidal-cat-view` onto
`c1af57cf89da5fb696a4aad6fa3a40eda6bd7a90`. The rebase has no conflicts;
full-library/test/install validation and the existing 123 temporary
universe/semantic checks passed with the unchanged `rocq-cats` switch.
The rebased task head before new mathematics is `c434d44`; original
`0683f04` is retained in the earlier historical delivery records.

[Global contexts](../../theories/Cat/Computational/Arrow/Global.v)
attaches a terminal-input computation to an unchanged ordinary input.
Its substitution, ordered-pairing and nested-context laws require only
selected finite products and the existing Arrow laws. Effects are neither
duplicated nor interchanged. This independently reusable foundation adds
no interface or model choice and retains separate category sizes.
All ten public declarations and six strict independent-category probes
passed temporary assumption inspection (16 reports, all closed under the
global context). The targeted module build passed. No permanent test,
shared toolchain change or integration-branch update was introduced.

[Global contexts](../../theories/Cat/Computational/Arrow/Global.v)

## Static interpretation into the original Arrow

This authorized slice continues on `monoidal-cat-view` after rebasing onto
`typeprop@c1af57cf89da5fb696a4aad6fa3a40eda6bd7a90`. The independently
reusable [global-context foundation](../../theories/Cat/Computational/Arrow/Global.v)
was pushed first in
[82e8efc](https://github.com/Godalin/rocq-cats/commit/82e8efca787a37e0626020fce7685c1dd30d548e).
[Static evaluation](../../theories/Cat/Computational/Arrow/Static.v)
adds exponentials only for ordinary internal-function evaluation. It
interprets a terminal-input internal function alongside its argument,
using the original Arrow's context action. Pure names, ordered internal
composition and context extension preserve the specified computation
Hom equality. No Monad, strength, effect interchange or representation
as a value-category endofunctor is assumed by this generic theory.

[StaticInterpret](../../theories/Instance/Set/StaticInterpret.v) packages the
comparison as `StaticInterpretF`, from the static category of the Arrow's
extracted Applicative into the original computation category. Its object
map is the original pure object map; no object-map injectivity or unused
ambient-object representation is assumed. The existing closed setoid
model requires a common carrier/equality level matched by the computation
hom-setoids. Computation-object size remains independent. This boundary
is fixed once, with repeated universe instances inferred.

`StaticInterpretPureIso` compares the interpreted static pure inclusion
with the original pure functor by identity components and explicit
identity inverses. Interpretation preserves composition and the same
chosen left context. All computational maps and inverse witnesses remain
transparent. This is an interpretation and operation-preservation result;
fullness, faithfulness, inverse reconstruction, ArrowApply/Monad and typed
syntax are not supplied by this slice. No new interface or chosen model
instance is introduced.

Full-library `dune build @all @runtest @install` passed with the unchanged
`rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0, Dune 3.23.1).
All 82 temporary assumption reports are closed under the global context:
24 public declarations, 38 strict universe probes and 20 concrete
constructions/result checks. The probes separate the two abstract
categories in both hom/equality orders, retain a smaller or larger
computation-object universe in the setoid interpreter, and separate
Reader/State environment levels below the closed-model bound. State
computations distinguish toggling before reading from reading before
toggling and check context, pure values and the pure comparison. Reader
values and context compute transparently. For the latter context check,
the temporary source first evaluates the result by `vm_compute`, then
compares the resulting small value; this avoids rechecking expanded
structure proofs when closing an ordinary equality. Library maps remain
transparent. Import probes confirm model choices require explicit enabling.
The earlier 123 checks passed again after rebase. The earlier 16 foundation
reports overlap this new 82-report batch and are not added again.

Strict bilingual HTML generated 344 modules per language and checked all
693 pages. All 54 bilingual documentation blocks and 48 public declaration
anchors in the three new modules were checked in their reading editions.
The inventory remains 97 interfaces (68 classes, 29 records), including
29 `Has*` classes. No permanent test, shared test alias or toolchain change
was added. Only this task branch was changed; `typeprop` remains owned by
integration. Batch PDF export remains with the integration session.

## Fully faithful inverse foundation for static reconstruction

This slice continues on `monoidal-cat-view` from `4d517d5`, with integrated
baseline `c1af57cf89da5fb696a4aad6fa3a40eda6bd7a90` unchanged.
[Functor.FullyFaithful](../../theories/Cat/Functor/FullyFaithful.v) constructs
a transparent inverse to a fully faithful functor restricted to its indexed
image objects. Type-valued fullness supplies preimages; faithfulness proves
respectfulness and the inverse laws. The two composites have natural
isomorphisms with identity components. No ambient object representatives or
additional choice principle are required.

[Setoid isomorphisms](../../theories/Instance/Set/Isomorphism.v) now also
construct an inverse from supplied Type-valued unique fibers. This uses
specified setoid equality. A native Hom isomorphism in one `SetCat` has a
common ambient bound, so the general inverse functor directly uses fullness
rather than identifying two categories' native hom universes. This
strict-probe finding is recorded in the existing `AGENTS.md` learnings.

Targeted builds passed in the unchanged `rocq-cats` switch. All 30 temporary
assumption reports are closed under the global context: ten public
constructions/laws, eighteen strict independent-category probes, and two
setoid ambient carrier/equality-order probes. Both category hom/equality
orders are separated, while the setoid lemma uses its stated common bound.
This independently reusable prerequisite adds no interface, chosen model,
permanent test or shared toolchain change. `typeprop` was not changed.

## Static representation and inverse reconstruction

This slice continues on `monoidal-cat-view` from the independently delivered
[fully faithful inverse foundation](https://github.com/Godalin/rocq-cats/commit/482cfa7235149bec40b2b51a4bc452fcf678390b),
with integrated baseline `c1af57cf89da5fb696a4aad6fa3a40eda6bd7a90` unchanged.
[The general criterion](../../theories/Cat/Computational/Arrow/Static.v)
requires invertibility of the actual global-function evaluation Hom maps,
retaining Type-valued inverse witnesses and independent value/computation
category sizes. Existing setoid inverse/fiber lemmas establish equivalence
with supplied unique representations in native Hom equality. The inverse
preserves pure names, execution-order composition and the original context
action. For every Applicative-generated static Arrow over selected finite
products and exponentials, the criterion follows from the existing
terminal-input value/function inverse. No setoid-base or well-pointedness
assumption is required for this general example.

[The setoid client](../../theories/Instance/Set/StaticRepresentation.v)
proves equivalence with full faithfulness of the existing static interpreter
by composing its Hom map with the existing exponential-unit isomorphism.
It reuses the native Hom-isomorphism criterion at the stated common closed-
model carrier/equality bound. The general fully faithful inverse supplies
`StaticReifyF`, identity-component unit/counit comparisons and the actual
`StaticRepresentationEq` in `CatCat`. Its target is the value-indexed
computation category, with no representatives selected for unused ambient
objects. Pure and context preservation are explicit; composition is
preserved by the functors. All computational maps and inverse witnesses
remain transparent. The computation-object universe remains independent
of its hom-setoids. No new interface or chosen model instance is added.

Full-library `dune build @all @runtest @install` passed with the unchanged
`rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0, Dune 3.23.1).
All 212 temporary assumption reports are closed under the global context:
39 new public declarations across the foundation and clients, 112 strict
universe probes, and 61 concrete constructions/result checks. The 112
probes comprise 20 foundation checks, 60 general-criterion checks,
28 native-client checks and four Reader/State environment checks.
They separate native hom/equality orders in the general theory and retain
computation-object levels both below and above the setoid client's common
bound. The earlier 30 foundation reports overlap this batch and are not
added again.

The concrete batch includes 18 VM reductions through transparent recovery,
interpretation, context and equivalence components. State examples use the
static Arrow generated by `StateA`, with an effectful internal function
that toggles Boolean state; they do not assume that an ordinary dynamic
state Arrow is static. Reader examples also recover values and context.
Temporary sources evaluate large constructions first and compare the
resulting small values. No temporary check is installed as a permanent
test or shared test alias, and no new axiom is introduced.

Strict bilingual HTML generated 347 modules per language and checked all
699 pages. The four reviewed modules contain 94 bilingual documentation
blocks and 82 public declaration anchors, all checked in their reading
editions; this count includes the two pre-existing setoid-isomorphism
declarations. The inventory remains 97 interfaces (68 classes, 29 records),
including 29 `Has*` classes. Only this task branch was changed; `typeprop`
and shared toolchains were not modified. Batch PDF export remains with
integration. ArrowApply/Monad and typed syntax remain subsequent work;
this slice claims a conditional category equivalence with explicit
operation preservation, not a blanket equivalence of computational
structure records.

## Pointwise strength foundation for ArrowApply

This independently reusable prerequisite continues on `monoidal-cat-view`
from `57f7fa1`, with integrated baseline
`c1af57cf89da5fb696a4aad6fa3a40eda6bd7a90` unchanged.
[Setoid strength](../../theories/Instance/Set/Strength.v) proves that every
supplied cartesian tensorial strength pairs a fixed ordinary context value
with the functor's result. Naturality and the unit equation suffice; the
proof uses no Monad or exponential, and compares values in specified
setoid equality. Any two supplied strengths consequently have equal
components, without equality of structure or law records. This will allow
Kleisli dynamic application to use an arbitrary supplied strong Monad.

The targeted module build passed with the unchanged `rocq-cats` switch
(Rocq/Stdlib 9.2.0, Dune 3.23.1). All six temporary assumption reports are
closed under the global context: the two public lemmas and four probes
with ambient carrier/equality universes strictly separated in both orders.
No interface, chosen model, permanent test or shared toolchain was added.
`typeprop` was not changed; full-batch validation follows with its clients.

## Lawful ArrowApply and Kleisli dynamic application

This finite slice continues on `monoidal-cat-view` from `57f7fa1`.
The independently reusable pointwise-strength prerequisite was delivered
first in [740e1c2](https://github.com/Godalin/rocq-cats/commit/740e1c2).
Initial validation used integrated baseline
`c1af57cf89da5fb696a4aad6fa3a40eda6bd7a90`; the synchronized handoff is
recorded below.
[ArrowApply](../../theories/Cat/Computational/Arrow/Apply.v) extends one
cartesian Arrow over the setoid base with dynamic application of an input
computation value. Its three laws are the pure-pairing, input-substitution
and postcomposition equations in
[Control.Arrow](https://downloads.haskell.org/ghc/9.6.7.20250131/docs/libraries/base-4.18.3.0/Control-Arrow.html),
after using the existing equation for `first` on pure arrows. This is a
certified interface, with Type-valued native Hom equality and all laws
supplied, rather than an operation class with unenforced laws.

The sole immediate parent is `ArrowApplyA :> Arrow`. Its pure functor and
object-map coercions are inherited through that parent, while morphism
mapping remains `fmap`. No inherited operations, context choices or
bypass coercions are duplicated. Fixed-computation application, its
respectfulness, postcomposition law and identity/value recovery are
separate derived operations and proofs. The value-recovery proof uses
only the class laws and ordinary Arrow equations; it assumes no
faithfulness of pure inclusion or pointwise extensionality of computation
arrows.

The interface explicitly matches computation hom carrier/equality levels
with its ambient setoids; its computation-object size is independent.
No selected exponential is needed. This is a native setoid presentation,
not a construction of internal computation-hom objects in every CCC.
[Kleisli dynamic application](../../theories/Instance/Set/KleisliApply.v)
uses respectful evaluation with the exact existing Arrow of an arbitrary
supplied strong Monad. Its input-substitution proof reuses pointwise
strength and ordinary Kleisli extension, so it works with that supplied
strength rather than replacing it by a concrete implementation. For
native Kleisli homs to be input objects, this client uses the stated common
carrier/equality bound. The underlying ordinary Monad is unchanged.
[StateArrowApply](../../theories/Instance/Set/State.v) is the explicit model
value, retaining independent state carrier/equality levels below that
bound. All computation data remain transparent.

Full-library `dune build @all @runtest @install` passed with the unchanged
`rocq-cats` switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0, Dune 3.23.1).
All 139 temporary assumption reports are closed under the global context:
18 new public interfaces/constructions/laws including the class fields,
66 strict universe and coercion probes, three native model signatures,
and 52 concrete constructions/result checks. The strict probes retain both
hom/equality orders with computation-object universes below or above
them, check the complete Arrow/functor/object-map coercion chain, separate
the strength foundation's ambient levels, and separate state carrier and
equality levels below the native model bound. The earlier six foundation
reports overlap this batch and are not added again.

The concrete batch includes 18 VM reductions after importing the public
modules. State examples dynamically choose between reading and toggling
then reading, based on a runtime ordinary input. Separate results check
input computation substitution versus output postcomposition, fixed
application, identity, pure pairing and the inherited views. Temporary
sources first compute large transparent constructions and then compare the
resulting small values. Import probes confirm that products, Monad,
strength and ArrowApply models require explicit selection. No temporary
check was installed as a permanent test or shared test alias; no new axiom
or shared toolchain change was introduced.

Strict bilingual HTML generated 350 modules per language and checked all
705 pages. The four reviewed modules have 72 bilingual documentation
blocks and 62 public declaration anchors, all checked in their reading
editions; these counts include the existing state-model declarations.
The inventory covers all 98 interfaces exactly once (69 classes,
29 records), including the unchanged 29 `Has*` classes. Only this task
branch was changed; `typeprop` remains owned by integration. Batch PDF
export remains with integration. This slice delivers the strong-Monad-to-
ArrowApply direction on its stated base. Recovering a Monad from
ArrowApply, dynamic representation comparisons and typed syntax remain
subsequent work; no equivalence of all computational structure records
is claimed here.

## ArrowApply handoff on the updated integration baseline

Before handoff, `typeprop` advanced to
`15a7ccf05eeee9d2c8d1691d3b47468e121c7978`, adding prism reconstruction
and the simplicial reading path. The task branch was rebased onto it
without conflicts. All 41 task commits retain their original contents in
`git range-diff`. The dynamic-application implementation `a1e26d6` is now
`416bde1`, the independent strength foundation `740e1c2` is now `884f957`,
and the previous static-reconstruction handoff `57f7fa1` is now `3d1f6c5`.
The new mathematical-illustration instructions were read; this batch adds
no mathematical diagram.

Full-library `@all @runtest @install` passed again on that baseline in the
unchanged project switch. All 139 reports and 18 concrete VM reductions
above passed again. The import probes now explicitly run typeclass search
to check that chosen products, Monad, strength and ArrowApply instances
are unavailable until selected. These reports replace, rather than add to,
the pre-rebase run. Strict bilingual HTML now covers 351 modules per
language and all 707 pages. The same 72 bilingual documentation blocks
and 62 public declaration anchors in the four reviewed modules were
checked again. The exact inventory remains 98 interfaces (69 classes,
29 records), including all 29 `Has*` classes. No source mathematics or
shared environment changed during synchronization; only the task branch
was rebased. Batch PDF export remains with integration.

## Dynamic Hom correspondence foundation

This independently reusable prerequisite continues on `monoidal-cat-view`
from `7df4d2f`, with integrated baseline
`15a7ccf05eeee9d2c8d1691d3b47468e121c7978` unchanged.
[Dynamic computations](../../theories/Cat/Computational/Arrow/Dynamic.v)
name an arrow by pure substitution of each ordinary input. Naming,
respectfulness and both naturality equations require only an ordinary
cartesian Arrow. Dynamic evaluation adds ArrowApply and applies the
selected terminal-input computation to the singleton. Its two
reconstruction laws follow from the existing application equations,
without assuming pointwise extensionality or pure-inclusion faithfulness.
Both native Hom-setoid maps are transparent and retain their distinct
native sizes; the eventual adjunction supplies any ambient lifting.

The targeted module build passed with the unchanged `rocq-cats` switch
(Rocq/Stdlib 9.2.0, Dune 3.23.1). All 55 temporary assumption reports are
closed under the global context: eleven public constructions/laws and
44 strict universe probes, separating hom/equality sizes in both orders
and placing computation-object size below or above them. No interface,
chosen model, permanent test or shared toolchain was added. `typeprop`
was not changed. The following Monad construction will reuse the existing
Hom-adjunction and adjunction-to-Monad theories.

## Dynamic Arrow adjunction and Monad recovery

This finite phase continues from the independently delivered dynamic Hom
foundation `557b048` on `monoidal-cat-view`, with integration baseline
`15a7ccf05eeee9d2c8d1691d3b47468e121c7978` unchanged.
[ArrowApplyAdjunction](../../theories/Cat/Computational/Arrow/Dynamic.v) reuses
`AdjunctionFromHom` with the pure indexed inclusion and the covariant
Hom functor at terminal input. The two supplied maps are the existing
transparent dynamic naming and evaluation. Ambient Hom lifting remains
inside the general adjunction constructor; computation-object, native
Hom carrier and equality levels remain independent. `ArrowMonad` reuses
`AdjunctionMonad` and compares its underlying functor to `ArrowGlobalF`
by an identity-component natural isomorphism. The unit agrees with the
existing pure global value; multiplication and extension are dynamic
composition. No Monad axiom is reproved for a concrete model.

[KleisliRecoveryIso](../../theories/Instance/Set/KleisliRecovery.v) recovers
the original supplied Monad from its `KleisliArrowApply`. Evaluation at
the singleton and constant computation give transparent inverse natural
transformations. Both preserve unit and multiplication, including the
required horizontal composite in the multiplication law; they are actual
inverse morphisms in the existing `MonadCat`. A separate comparison
preserves continuation extension and its effect order. This native
Kleisli client uses the stated common carrier/equality bound, retaining
independent smaller state carrier/equality levels. No exponentials,
effect commutation, equality of functions/law fields or new assumption
is introduced. This proves the Monad round trip for a supplied Kleisli
model; arbitrary ArrowApply reconstruction, compatibility with every
additional computational structure and typed syntax remain subsequent work.

Full-library `@all @runtest @install` passed in the unchanged `rocq-cats`
switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0, Dune 3.23.1). All 215 temporary
assumption reports are closed under the global context: 35 public
constructions/laws, 124 size probes and 56 concrete-model helpers/results.
The probes cover both strict native Hom/equality orders, computation-object
size above and below those levels, the common native Kleisli bound, and
both strict state carrier/equality orders below it. Import-only typeclass
search confirms that chosen products, Monad and ArrowApply remain explicit.
These 215 reports include the earlier 55 foundation reports, not another
55 in addition. All 24 Boolean-state VM reductions pass, covering return,
nested flattening with the updated state passed to the inner computation,
continuation selection and sequencing, both recovery maps and inverse laws,
the underlying functor comparison and both Monad-isomorphism maps.
Concrete expressions use an abstract value-level join helper to avoid
expanding the entire derived structure during component type inference;
all maps and the final checks remain transparent. All checks are temporary;
no redundant permanent tests or shared test configuration were added.

Strict bilingual HTML covers 354 modules per language and all 713 checked
pages. The three reviewed modules' 78 language-specific documentation
blocks and 70 public declaration anchors were checked individually in the
corresponding reading editions. The inventory remains exactly 98 interfaces
(69 classes, 29 records), including all 29 `Has*` classes. Only the task
branch is changed; batch PDF export and `typeprop` remain with integration.

## General foundations for dynamic reconstruction

Continue the authorized serial #35 task on `monoidal-cat-view` from
`874ed08`, with integration baseline `15a7ccf05eeee9d2c8d1691d3b47468e121c7978`.
[The general Kleisli comparison](../../theories/Cat/Monad/Kleisli.v)
uses inverse transposition and counit multiplication to preserve composition.
Its Type-valued full-faithfulness witness keeps transposes as preimages;
it does not assert essential surjectivity onto an arbitrary adjunction
target. [Explicit setoid strength](../../theories/Instance/Set/Strength.v)
maps pairing with an ordinary fixed value through any endofunctor. Functor
laws give naturality/coherence, while unit and multiplication naturality
give an explicit strong view of any supplied setoid Monad. Neither import
registers a chosen model; no new interface or axiom is introduced.

The two foundations are delivered independently before the reconstruction
client. Full-library `@all @runtest @install` passed with the unchanged
`rocq-cats` switch (Rocq/Stdlib 9.2.0, Dune 3.23.1). All 27 temporary
assumption reports are closed: seven public constructions/laws and 20
strict universe probes, covering independent category sizes in four
orders and both strict setoid carrier/equality orders. Import-only probes
confirm strength and strong Monad choices remain explicit. No permanent
tests, shared test configuration, `typeprop` or shared environment changed.
Full reading-edition validation is deferred to the completed finite phase;
batch PDF export remains with integration.

## Native dynamic Arrow reconstruction

This finite phase continues on `monoidal-cat-view` from the independently
pushed comparison/strength foundation `84fb5c9`, retaining integration
baseline `15a7ccf05eeee9d2c8d1691d3b47468e121c7978`.
[Dynamic recovery](../../theories/Cat/Computational/Arrow/Dynamic.v)
reuses `SetStrongM` to give the exact existing `ArrowMonad` canonical
strength. Its reconstructed Arrow reuses `KleisliArrow`. Evaluation is
`AdjunctionKleisliF` specialized to `ArrowApplyAdjunction`; naming inherits
its functor laws from `FullyFaithfulInverseF`. Two explicit natural
isomorphisms exhibit the equivalence between the reconstructed Kleisli
category and the original computation category indexed by values.
Their object maps are identity on those indices. This does not select
representatives for all ambient computation objects or assume pure-arrow
faithfulness. The original native Hom/equality levels and computation-object
size remain independent throughout this comparison.

Both directions preserve the Arrow interface's pure lifting, sequential
composition and ordinary left-context action. The context argument first
extracts [arrow_dynamic_name_context](../../theories/Cat/Computational/Arrow/Dynamic.v)
under only an ordinary Arrow. It reuses the existing inverse-isomorphism
square theorem and context naturality, rather than requiring dynamic
application or a Monad for the pointwise formula. At the stated common
native carrier/equality bound, `ArrowKleisliApply` reuses the existing
Kleisli application on the same strong Monad. The application comparison
maps original computation values through naming, and its inverse maps
reconstructed values through evaluation. Both equations use the original
Hom equality. No exponential choice, effect interchange, equality of
functions/proof records or new axioms are introduced. This completes this
native dynamic Arrow reconstruction slice. Compatibility of the different
derived Applicative conversions remains subsequent semantic work; typed
syntax, Day convolution and profunctor presentations are not part of it.

Full-library `@all @runtest @install` passed with the unchanged `rocq-cats`
switch (Rocq/Stdlib 9.2.0, OCaml 5.3.0, Dune 3.23.1). All 225 temporary
assumption reports are closed: 25 public constructions/laws, 122 strict
size probes and 78 concrete-model helpers/results. This includes the
27 independently reported foundation checks. The probes cover independent
category levels in four orders, both native carrier/equality orders,
computation-object size above or below them, both native application
object orders, and both strict state carrier/equality orders below a common
ambient bound. The weaker context law is also checked with ordinary
Kleisli Arrows. Import-only searches confirm that strength, strong Monad,
products and Monad choices remain explicit.

All 28 transparent Boolean-state VM reductions pass: both functors and
round trips, pure lifting, sequencing in two distinguishable orders,
context in both comparison directions, dynamically supplied application,
both natural-isomorphism components and inverse components, and canonical
strength on the original and recovered Monads. Abstract value-level
helpers fix the operation boundaries before concrete specialization;
all final computations remain transparent. Checks are temporary; no
permanent test or shared test configuration is changed.

Strict bilingual HTML covers 357 modules per language and all 719 checked
pages. The four reviewed modules' 86 documentation blocks and 72 public
declaration anchors were checked individually in the corresponding
reading editions. The complete inventory covers exactly 98 interfaces
(69 classes, 29 records), including all 29 `Has*` classes, without missing
or duplicate declarations. Only this task branch changed; `typeprop`,
shared toolchain settings and batch PDF exports remain with integration.

## Dynamic reconstruction handoff on the updated baseline

Before handoff, integration advanced to
`5631b64a7ad8e854638cd116169ca6ef5ceee761`. The task branch rebased without
Git conflicts; `git range-diff` preserves all 46 task commits' contents.
The independent comparison/strength foundation `84fb5c9` is now `2c4565f`,
dynamic reconstruction `5fb79f5` is now `4a378ac`, the earlier Monad
recovery `874ed08` is now `e133b8d`, and dynamic Hom foundation `557b048`
is now `1ddbc48`. The current integrated instructions were read. No
mathematical diagram was introduced by this slice.

Three upstream additions had proof references to algebra names moved by
the task's previously authorized hierarchy refactor. The commutative
coefficient, group-equation and cocycle modules now reference
`semigroup_assoc` and `magma_mul_proper`; group-equation laws and their
bilingual diagram labels use `magma_mul_l_resp`/`magma_mul_r_resp`.
The new upstream coefficient universe regression has the same two map
reference updates. These are adaptations of the earlier rename to new
clients: upstream operations, public declarations, mathematical conditions
and test assertions are retained, with no compatibility aliases or new
regression files. No shared test configuration is changed.

Full-library `@all @runtest @install` passed on the new baseline with the
unchanged toolchain. The preceding 225 assumption reports and 28 transparent
VM reductions passed again, and 31 additional reports for the adapted
upstream clients are also closed under the global context: 256 reports
in the final run. These replace, rather than accumulate with, the old
baseline's checks. Strict bilingual HTML now covers 363 modules per
language and all 731 checked pages. The same four task modules' 86
language-specific documentation blocks and 72 public anchors were checked
again. The inventory covers all 100 interfaces exactly once (70 classes,
30 records), including all 29 `Has*` classes; the two additions belong to
the new upstream batch. Only the task branch is updated; integration
retains `typeprop` and batch PDF export.

## Direct Applicative compatibility

This finite #35 slice continues the authorized serial task on
`monoidal-cat-view`, from `c0e6fb1` on integrated baseline
`5631b64a7ad8e854638cd116169ca6ef5ceee761`. It closes the outstanding direct
Applicative comparison in E. Day convolution, profunctor/end/coend theory and
free constructions are subsequent phases; no typed calculus is introduced.

[Applicative morphisms](../../theories/Cat/Applicative/Morphism.v) are Type-valued
pure/pairing preservation laws on supplied natural transformations. The
shared theory proves stability under designated equality, identity, composition
and the same chosen natural inverse. It derives lax-unit, arbitrary binary
lifting and contextual pure preservation; selected exponentials add application
preservation. The abstract theory uses named terminal/product choices and
independent category sizes, with no extra strength or function-equality axioms.

[Dynamic comparison](../../theories/Cat/Computational/Arrow/Dynamic.v)
reuses pure, composition and context preservation to compare first, split and
fanout with the recovered Kleisli Arrow. The weaker terminal-input naming law
in [Dynamic](../../theories/Cat/Computational/Arrow/Dynamic.v) needs only an
ordinary Arrow. Combined with the existing general Kleisli fanout comparison,
it proves the two Applicatives' pairing comparison. The existing identity
natural isomorphism preserves all operations in both directions. Computation
object, native carrier and equality levels remain independent. This part needs
neither exponentials nor the common native size bound used by application models.

[Native Kleisli compatibility](../../theories/Instance/Set/KleisliApplicative.v)
retains the existing native recovery model's common carrier/equality bound.
It repackages the original evaluation/constant components on the actual
Applicative functors and reuses their naturality and inverses, rather than
requiring definitional equality of functor law records. It preserves the
original supplied strength and ordered pairing. Both comparison triangles
commute with Monad recovery. Composing the comparisons proves forward and
inverse Applicative preservation for the recovered Monad with canonical
strength. [Static recovery](../../theories/Instance/Set/StaticArrow.v) exposes its
previously proved comparisons through the shared preservation predicate.

Proofs first compare explicitly typed abstract computation values, cancel
identity comparison maps at the morphism level, then instantiate the values.
This avoids expanding computations stored in lifted products during conversion.
Proof-only opacity for pairing/fanout is local and restored before clients;
all comparison maps retain transparent computational bodies.

Validation with the unchanged `rocq-cats` switch (Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1): full-library `@all @runtest @install` passes.
All **205 temporary assumption reports** are closed: 124 public/strict-size
and application probes, and 81 concrete-model helpers/results. Size probes
cover both strict hom/equality orders with objects above/below them, independent
dynamic computation sizes, and both strict State carrier/equality orders below
the native common bound. Import-only probes select no default Monad, strength
or Applicative. **30 transparent Boolean-state reductions** cover pure,
result maps, ordered pairing in both distinguishable effect orders, binary
lifting, application, both comparison directions, round trips and comparison
triangles. No permanent tests, shared test configuration, environment changes
or concrete model-law proofs are added. Strict bilingual HTML covers 366 modules per language and 737 checked pages;
batch PDF export remains with integration.

The agreed completion boundary now includes direct definitions/models,
monoid-object characterizations and coherent connections, followed by the
general free-monoid construction and justified free Monad/Applicative/Arrow
instances with universal interpretation and uniqueness. Each specialization
must prove its size/existence/preservation hypotheses. Typed language syntax
and optional Cayley representations are outside that boundary.

### Direct-comparison handoff on the updated baseline

Before handoff, `typeprop` advanced by two upstream commits to
`8db08e33d0e859c9a62980a2c313b4fb00398607`. The task's 48 commits rebase
without conflicts; `git range-diff` confirms identical contents, including
implementation `8351ed5` becoming `89a6bee`. The following synchronization
adaptations are separate from those unchanged commits:

- [Cocycle completion](../../theories/Algebra/Group/Cocycle.v) uses the existing
  magma respectfulness and semigroup associativity names. Its operations,
  hypotheses, construction names and mathematical conclusions are retained.
- [The new upstream size regression](../../tests/cocycle/model/Universes.v)
  changes only two explicit Monoid universe-instance orders to match the
  inherited hierarchy. The carrier/equality profiles remain interchanged,
  law witnesses retain their independent upper bound, and every strict
  inequality and test assertion is retained. No test file or alias is added
  by this adaptation, and shared test configuration is untouched.

The final local validation on this baseline includes full-library
`@all @runtest @install`, the same 30 transparent State reductions and all
245 closed temporary assumption reports: 124 general/strict-size probes,
81 concrete-model helpers/results and 40 public declarations in the new
upstream cocycle-completion and simplicial-model modules. Strict bilingual
HTML covers 370 modules per language and 745 checked pages. In the five
affected comparison/recovery modules, all 126 language-specific documentation
blocks and 110 declaration anchors are checked against the rendered pages.
The exact inventory remains 100 interfaces (70 classes, 30 records), including
all 29 `Has*` classes. Batch PDF export remains with integration. These final
checks replace the earlier-baseline counts; they are not cumulative totals.

### Universal end/coend interfaces

[Wedges](../../theories/Cat/End/Wedge.v) retain diagonal legs and their
Type-valued commuting equations. A wedge is the special dinatural family
needed here; this does not introduce composition of arbitrary dinatural
transformations. [Ends](../../theories/Cat/End/Core.v) separate the candidate
universal property from a selected apex and wedge. Mediators are transparent;
their computation, uniqueness and natural-transformation action use the
specified hom equality. Object comparison reuses terminal-object uniqueness
in the wedge category, including the projection equation of that comparison.

[Cowedges](../../theories/Cat/Coend/Wedge.v) and
[coends](../../theories/Cat/Coend/Core.v) store only the corresponding opposite
wedge and end. [The domain adapter](../../theories/Cat/Functor/OppositeProduct.v)
compares a product of opposite categories with the opposite product. Reversing
a mixed-variance bifunctor changes its index category to the opposite category;
it does not swap the object pair. Injection, descent and comparison laws are
wrappers around the end theory. Natural isomorphisms retain computed inverse
maps on both ends and coends. No equality of category records, component
functions or retained law witnesses is required.

This is an existence-conditional foundation. It asserts neither that every
category has these objects nor that object-indexed constructions fit into one
fixed universe. Abstract interfaces retain independent object, hom-carrier and
hom-equality levels; law witnesses may require separate upper bounds. Concrete
product/equalizer and setoid models, size/existence conditions for Day and
profunctor composition, and the later monoid/free constructions remain work
for subsequent batches. In particular, the full category of setoids at one
fixed carrier/equality size is not thereby a small indexing category for
coends in that same category.

Prior art includes Wiegley's pinned
[wedge interface](https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Structure/Wedge.v),
[end interface](https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Structure/End.v)
and [opposite-end coend interface](https://github.com/jwiegley/category-theory/blob/99869fd8d9117e900dea862d8612033848aa01dd/Structure/Coend.v).
The present implementation follows the library's existing cone/terminal
interfaces and reuses its general opposite and natural-transformation theory.
It does not claim the mathematical construction as new.

### End/coend existence from selected products and equalizers

[Constrained-family factorization](../../theories/Cat/Product/Equalizer.v)
extracts the common argument used by ordinary limits and ends: a family
determines a product arrow, and an equalizing product arrow factors uniquely
through a candidate equalizer. The existing
[limit construction](../../theories/Cat/Limit/Construction.v) now reuses this
lemma without changing its public statements or selected objects.

The [end construction](../../theories/Cat/End/Construction.v) requires only
the product of diagonal values, the product of one off-diagonal value per
arrow, and an equalizer of the resulting two constraint maps. Arrow indices
retain endpoints and a morphism, without storing hom-equality witnesses.
`ProductsEqualizerEndOf` accepts that one candidate equalizer; the convenience
constructor additionally accepts chosen equalizers. Neither requires limits
of unrelated diagrams. The
[coend construction](../../theories/Cat/Coend/Construction.v) adapts selected
coproducts to opposite products and reuses the same end construction, including
its universal mediator and uniqueness proof. It does not build a second
universal-property proof or compare duplicate constructions.

The explicit [setoid end model](../../theories/Instance/Set/End.v) reuses
dependent products and equalizers. Sufficient bounds for this construction
are that the index category's object and hom-carrier levels fit its target
equality level, which in turn fits the target carrier level. The explicit
[setoid coend model](../../theories/Instance/Set/Coend.v) reuses indexed sums
and generated coequalizer equality. Here the index object and hom-carrier
levels fit the target carrier level, which fits the target equality level;
generated equality may retain intermediate representatives. In both models
the index category's hom-equality level stays independent. These bounds are
sufficient conditions for the particular models, without a resizing axiom
or a claim of optimal necessity. Importing either module does not register
a global choice.

This batch supplies the promised existence foundation. It does not assert
that a full fixed-size setoid category can index coends in itself. Day and
strong-profunctor constructions must state their own actual size and
existence conditions. Their monoid characterizations, coherent comparisons
and suitably conditional free constructions remain subsequent work.

### Covariant Day convolution and its natural universal correspondence

The [Day kernel and output functor](../../theories/Cat/Day/Core.v) reuse Hom,
explicit universe lifting, pointwise products and the integrated coend
theory. The kernel pairs a Hom weight from the binary result to the output
with the two input values. Only a binary functor is needed here; a monoidal
category supplies its tensor bifunctor when constructing coherence later.
Neither tensorial strength nor invertible comparison maps are assumed.
`HasDay` selects only this family's particular pointwise coends, keeping
the existence condition explicit.

[Input maps](../../theories/Cat/Day/Map.v) act independently on the value
coordinates and commute with postcomposition in the output coordinate.
They preserve the specified natural-transformation equality, identities
and composition. A uniformly supplied family of choices assembles these
maps into `DayTensorF`, a bifunctor on the functor category. This is not yet
a monoidal structure: unitors, the associator and their coherent laws are
separate subsequent obligations.

The [universal correspondence](../../theories/Cat/Day/Universal.v) treats
weighted value pairs as generators. Changing their indices uses the coend's
gluing equation; changing their output postcomposes their weight. A natural
binary operation extends by evaluating the operation and applying the
output functor to that weight. Conversely, a transformation out of the
convolution restricts to generators with identity weights. Both round trips
hold in the specified natural-transformation equality, and an extension is
unique with its prescribed restriction. All maps and witnesses remain
transparent; no equality of functions or law fields is used.

The [explicit setoid model](../../theories/Instance/Set/Day.v) reuses the
integrated setoid coend model. Sufficient bounds are `o,h ≤ u ≤ p` and
`e ≤ p`, where `o,h,e` are base object, hom-carrier and hom-equality levels
and `u,p` are target carrier/equality levels. The Hom weight explains the
additional equality bound. These are sufficient conditions for this model,
not assertions that every fixed-size full setoid category admits Day
convolution in itself. Target universes are fixed explicitly at structure
and transformation boundaries: compilation alone can otherwise accept an
unnecessarily identified pair of native and ambient sizes. Strict probes
check both object/hom orders, equality levels below or above the carrier,
and conditional abstract choices with objects larger than the output levels.
No resizing or globally registered model choice is introduced.

The monoidal coherence, Day-monoid/lax-monoidal correspondence and its
operation-preserving connections remain open. Strong profunctors must carry
their own coherent context action; that strength is not supplied by this
Day construction. The final required free constructions remain later work.

### Representable Day units and natural unit isomorphisms

The [unit construction](../../theories/Cat/Day/Unit.v) uses the explicitly
raised covariant representable at a proposed unit object. Its left unitor
needs only a binary functor and an invertible natural left unit map;
the right construction needs the corresponding right unit map. They do
not require an associator, symmetry, cartesian products in the base,
strength or preservation properties of the input functor. Their existence
conditions remain exactly the selected convolutions involving this
representable and the input functor.

Both forward transformations reuse the natural Day extension. Their
inverses insert the identity representable arrow with the supplied base
unitor as weight. The two inverse equations follow from the base inverse
laws, the Day generator computation and coend gluing. No new quotient,
universal-property construction or equality between law witnesses is used.
The construction retains transparent inverse maps and their computation
equations on arbitrary weighted generators.

The general [generator-map law](../../theories/Cat/Day/Universal.v) exposes
how a convolution map changes both values while retaining the weight.
It supplies naturality of these unitors in the input functor. Naturality
of their inverses reuses the existing inverse-square theorem. With a
uniform explicit family of convolution choices, the unitors assemble
into natural isomorphisms on the functor category itself, ready for the
existing bifunctor-based monoidal constructor. The original monoidal
tensor and its selected unit maps instantiate these interfaces directly.

Ambient carrier and equality levels stay fixed independently, with the
same Hom-weight and coend size conditions as the preceding Day model.
Only the coends at the functors concerned are assumed in the individual
unit laws; a uniform family is needed only for the functor-category
packaging. No chosen structure is registered by importing the module.
This establishes the unit part, not the associator, triangle or pentagon.
Their coherence, the Day-monoid/lax-monoidal characterization, strong
profunctors and the required free constructions remain subsequent work.

### Products preserve specified setoid coends

The [product/coend construction](../../theories/Instance/Set/CoendProduct.v)
assumes only a selected coend of a setoid-valued bifunctor and a fixed
setoid parameter. A respectful family of cowedges descends separately at
each parameter. Respectfulness of the resulting map in both coordinates
follows from the original coend's uniqueness and respectful mediator.
Paired injections jointly distinguish outgoing maps, giving computation,
uniqueness and invariance under pointwise equality of the input family.
Neither function equality nor equality of respectfulness witnesses is used.

Applying that one parameterized construction to a product cowedge shows
that taking a fixed right product preserves the specified coend. A fixed
left product reuses the same mediator after coordinate exchange. Both
choices are explicitly enabled definitions, not globally registered
instances. When a product kernel already has another chosen coend,
universal object uniqueness supplies a canonical comparison isomorphism
with a transparent inverse and injection/reinsertion equations. The
comparison does not identify the selected objects or their law records.

Carrier and equality universes remain independent. The abstract result
requires no ordering between them because it uses parameterized descent,
not an internal function object. Existence is still explicit: it does not
construct a coend for every bifunctor. Instantiating the existing generated
setoid coend model retains its sufficient bounds on index objects and
arrows below the target carrier, and carrier below equality; the index
hom-equality level remains independent. No resizing or fixed-size full
setoid self-indexing assertion is introduced.

This is a prerequisite for descending through the inner coend of a nested
Day convolution while retaining its other values and weights as parameters.
It adds no Day associator or triangle/pentagon theorem. Those dependent
constructions follow after this foundation integrates; the agreed monoid
characterizations, strong profunctors and free constructions remain open.

### Natural Day associativity from the specified four convolution families

[Parameterized extension](../../theories/Cat/Day/Parameter.v) keeps a fixed
setoid value outside a Day convolution. Slicing a parameterized natural
binary operation gives the existing ordinary Day extension; respectful
product/coend descent reassembles the slices. Computation, uniqueness and
parameter/output comparison laws follow from the same universal property.
There is no internal function object and no new carrier/equality ordering.

[Nested extension](../../theories/Cat/Day/Iterated.v) then treats either
bracketing of three inputs. The inner pair extends with the remaining
value as a parameter; the outer pair uses ordinary Day extension. Ordered
weight computation and gluing show that every doubly weighted generator
comes from an identity triple under the output action. Consequently,
natural transformations are determined on identity triples. Left and
right output bracketings use the same triple-indexed source, retaining
all three inputs in their original order.

The [Day associator](../../theories/Cat/Day/Associator.v) needs only a binary
functor and its supplied natural associativity isomorphism. Transport the
right ternary generator by the inverse base map, then extend it through
the left nesting. The reverse extension uses the forward base map. Joint
distinction reduces both inverse laws to the base inverse laws. Each map
is natural in the output and in all three input functors. Inverse input
naturality reuses the general inverse-square theorem. Uniform explicit
convolution choices package these maps as a natural isomorphism between
the tensor bracketings on the functor category.

Individual associators require only the two inner and two outer selected
convolutions. Their ambient carrier/equality levels and the Hom-weight
bounds are those of the original Day construction; actual generated
models retain their original sufficient size conditions. No unit,
symmetry, strength, equality between functor records or additional axiom
is used. A general first-coordinate product-parameter transformation
reuses the existing second-coordinate naturality through an explicitly
flipped diagram and has the right nested extension as a client.

This establishes natural associativity and its transparent inverse, not
the triangle or pentagon. Those require the corresponding base coherence
and separate proofs before a complete Day monoidal structure is claimed.
The Day-monoid/lax correspondence, strong profunctors, coherent connections
and conditional free constructions remain subsequent work.

### Coherent Day convolution and the explicit monoidal assembly

[Day coherence](../../theories/Cat/Day/Coherence.v) separates the two coherence
assumptions. The triangle uses just the base triangle, the supplied natural
unit/associativity isomorphisms and the five selected convolutions in its
source, intermediate objects and target. The base equation says that left
unit insertion followed by inverse associativity equals right unit insertion
in the other coordinate. Ternary generator distinction lifts that equation
to the two Day routes. No base pentagon is needed by this theorem.

The pentagon requires the base pentagon and the twelve selected binary
convolutions used by the five bracketings of four inputs. A fourth-input
distinction lemma reuses ternary distinction and parameterized coend descent.
It selects only the three convolutions of the fully left-associated source.
Both routes on identity quadruples become the same final generator with
different result weights. Since Day associativity uses the inverse base
map, these weights satisfy the inverse base pentagon. Inverse uniqueness
derives that equation from the forward base pentagon without equating law
witnesses. This theorem needs no unit, symmetry or strength.

[Day monoidal assembly](../../theories/Cat/Day/Monoidal.v) takes a coherent
binary functor with unit and uniform explicit convolution choices. It reuses
`BifctMonoidal`, the original `DayTensorF`, representable `DayUnitF`,
unitors and associator with their transparent inverses. Tensor interchange
comes from the bifunctor; its reconstructed tensor action agrees with the
supplied Day action in natural equality. Identity components compare the
derived tensor functor with the original one, without equality of functor
records. `MonoidalDay` also starts directly from a supplied monoidal category,
reusing its existing bimap pentagon and triangle. Importing these modules
registers no global convolution choices.

All ambient carrier/equality and base Hom-weight bounds remain those of the
original Day construction. Conditional coend choices add no extra ordering
between ambient carrier and equality levels. The existing generated setoid
model retains its sufficient bounds: base objects and Hom carriers at most
the output carrier, that carrier at most output equality, and base Hom
equality at most output equality. No assertion of fixed-size full setoid
self-indexing, resizing, internal function objects or new axioms is added.
Pointwise coherence boundaries let concrete clients supply large
representatives without unfolding their stored computations during inference.

This completes the Day tensor/unit/associativity coherence layer under its
stated hypotheses. The Day-monoid/lax correspondence, strong profunctors,
coherent computational connections and conditional free constructions remain
subsequent work; they are not implied by this monoidal assembly alone.

### Day monoids and native lax monoidal operations

[Day monoid characterization](../../theories/Cat/Day/Monoid.v) starts from a
supplied monoidal base and explicit uniform Day convolution choices. The
value target uses the existing selected terminal object and products on
setoids. Lifted covariant Yoneda, via the existing opposite-presheaf proof,
identifies a map from the representable Day unit with a value at the base
unit. The existing Day restriction/extension correspondence identifies a
multiplication with its natural binary operation. No new universal property
is rebuilt in a concrete model.

`day_monoid_laws` equates the three fixed-data Day monoid diagrams with the
native lax unit and associativity equations. The unit equations use the
transparent inverse Day unitors; the multiplication equation uses ternary
generator distinction and inverse associativity. The reconstructed Day tensor
map is compared with the universal Day action in natural equality. The
predicate `is_day_lax` compares fixed operations; the complete structure
remains the existing `LaxMonoidalFct`, with no staging data record.

`LaxDayMonoid` and `DayMonoidLax` construct both structures with exactly the
same underlying functor. Both units and both binary operations survive the
round trips in designated equality, without identifying law or functor
records. All mediators and conversion data stay transparent. The generic
lax-functor preservation of monoid objects remains available separately;
applying it to the base unit monoid alone would produce an object at that
unit, not this monoid in the functor category.

Ambient carrier and equality universes stay independent, with the original
Day weight bounds and explicit existence input. Conditional choices add no
ordering between those ambient levels. The generated model retains its
sufficient bounds `o,h ≤ u ≤ p` and `e ≤ p`; no resizing or fixed-size full
setoid self-indexing is asserted. Importing this optional module enables no
global selected structure and changes no coercion or notation.

This bounded stage proves the object/operation correspondence. Packaging
monoidal natural transformations and the resulting categorical comparison,
the connection with the direct Applicative interface, strong profunctors and
conditional free constructions remain separate subsequent stages.

### Monoidal natural transformations as an independent prerequisite

[Monoidal natural transformations](../../theories/Cat/Monoidal/Natural.v)
compare lax monoidal functors at fixed named source and target structures.
`is_lax_monoidal_hom` retains Type-valued unit and tensor preservation on a
supplied natural transformation. Equality is the existing natural equality;
no equality of functor or preservation records is used. Preservation is
stable under equal transformations, identity and vertical composition. A
specified natural inverse preserves the same comparisons by cancellation;
ordinary morphisms need not be invertible.

`LaxMonoidalFctCat` uses the existing subset-setoid construction for its
hom-sets. It stores the transformation and its preservation witnesses while
comparing only the transformation. `LaxMonoidalForgetF` retains the exact
underlying functors and transformations and is faithful by that equality.
Source and target object, Hom and equality levels remain independent; law
universes supply the needed bounds separately.

The existing [monoid transport](../../theories/Cat/Monoidal/Transport.v) is an
actual general client. A monoidal transformation induces monoid
homomorphisms between the transported monoids. These components form
`LaxMonoidN`, natural in source monoid homomorphisms, without re-proving
transported monoid laws. Identity and vertical composition are preserved in
specified equality; `LaxMonoidTransportF` packages this variation into a
functor to the category of monoid-transport functors. No strength, symmetry,
cartesian structure, coends or chosen model is required by the general result.

This independent prerequisite does not yet package the Day/lax morphism
comparison or its categorical equivalence. Those dependent constructions and
the direct Applicative connection remain subsequent stages. Existing lax
functor, monoid and Day interfaces and their selected structures are unchanged.

### Day monoids and lax functors on morphisms and categories

[Day morphisms](../../theories/Cat/Day/Morphism.v) first compares preservation
on candidate operations. Lifted Yoneda detects a unit square at the identity
value, with no convolution assumption. The multiplication square is detected
on ordinary pairs using the existing Day restriction/extension inverse laws.
Only the two endpoint convolutions are selected by this binary result; no
unit, associativity or coherence is assumed at this step.

For a supplied monoidal base and the same uniform Day choices as before,
`day_monoid_hom_laws` identifies monoid homomorphisms with monoidal natural
transformations of the restricted lax functors. `lax_day_monoid_hom` gives
the converse presentation, reusing the existing operation round trips.
The reconstructed tensor action is compared with `DayMapN` in natural
equality, without identifying tensor-functor or preservation records.

[The categorical comparison](../../theories/Cat/Day/Comparison.v) extends the
two existing object conversions to `LaxDayMonoidF` and `DayMonoidLaxF`.
Their arrow actions retain exactly the supplied underlying natural
transformation and transfer only its preservation witnesses. The unit and
multiplication round trips make identity components into homomorphisms.
They assemble into natural isomorphisms in both directions; the lax inverse
uses the independently established general inverse-preservation theorem.
`day_lax_monoid_equiv` packages the resulting equivalence in the existing
`CatCat`. The chosen unit and counit also satisfy both comparison triangles.
There is no equality of functor, monoid or law records.

All comparisons retain the original explicit Day existence input and
independent ambient carrier/equality levels. The actual generated model
still uses `o,h ≤ u ≤ p`, `e ≤ p`; conditional choices do not impose an
additional ordering of the ambient levels or require self-indexing the full
setoid category. The optional modules add no chosen structure, global
instance, coercion, notation or axiom. Pointwise operation boundaries keep
type inference from normalizing unrelated stored law witnesses.

This completes the Day-monoid/native-lax categorical correspondence under
its stated choices. The link to the direct Applicative interface, strong
profunctors, coherent computational connections and justified conditional
free constructions remain subsequent stages of the broader semantic line.

### Native setoid pure as a prerequisite for the Applicative–Day connection

[Native lax Applicatives](../../theories/Instance/Set/LaxApplicative.v) recover
pure values from the unit of a cartesian lax setoid endofunctor. First,
`SetPureN` maps any specified singleton value along constant respectful maps.
Functor composition proves naturality; naturality at constants proves that
any other supplied pure transformation with the same singleton value agrees
in designated natural equality. This first result does not use lax data.

`SetLaxA` takes exactly the supplied lax structure as its parent. Its pure
unit law follows from functor identity, and pure pairing uses only tensorator
naturality and the left lax unit equation. No strength is selected and no
coend is assumed. The existing Applicative laws therefore apply directly,
including contextual binary lifting and application when exponentials are
separately available. Neither ambient carrier/equality universe is ordered
against the other by this construction.

Unit-preserving natural transformations preserve the recovered pure values.
`set_lax_applicative_hom` identifies the existing Applicative and monoidal
preservation predicates for these explicit lifts; `set_applicative_hom_lax`
does the same for any supplied native Applicatives. Binary preservation
reuses the existing comparison of derived tensor action with product maps.
`set_applicative_pure_roundtrip` recovers the original pure, and identity
components preserve both directions' operations. The inverse comparison
reuses general Applicative inverse preservation. No equality of structures,
functions or law records is required.

This independently reusable prerequisite is specific to the native setoid
category. An arbitrary categorical lax endofunctor is not silently given a
pure map. The dependent Day connection still requires explicit convolution
choices: no fixed-size full-setoid self-indexing coend, resizing principle or
new global model choice is claimed. Its packaging is a subsequent bounded
stage after this prerequisite's integration; strong profunctors and free
constructions remain outside this batch.

### Direct Applicatives and Day operations on native setoids

[The direct connection](../../theories/Instance/Set/DayApplicative.v) reuses the
integrated native pure reconstruction and Day/lax correspondence. Its weak
operation interfaces first extend the inherited lax unit by lifted Yoneda
and the tensorator by the Day universal correspondence. Constants in the
representable unit compute to the original pure values; weighted binary
generators compute to the original binary lifting. Unit preservation needs
no convolution choice. Binary preservation needs only the two endpoint
self-convolutions, without uniform choices or a Day monoidal assembly.

Under explicit uniform choices, `ApplicativeDayMonoid` and `DayMonoidA`
retain the underlying functor and reuse the existing structure conversions.
Their two homomorphism theorems identify exactly the existing preservation
predicates on the same natural transformation. Pure recovery uses singleton
uniqueness and the accepted lax-unit round trip. Tensorator, all binary
liftings and native application survive the round trip; Day unit and
multiplication use their already proved round trips. Identity comparisons
preserve operations in both directions, reusing the existing inverse laws.
No duplicate structure laws, equality of records or proof fields are added.

The native specialization has an explicit common ambient carrier/equality
bound. Existing Day kernels lift Hom weights to their value levels. Native
respectful function carriers and pointwise equality witnesses involve both
ambient levels, so applying these interfaces to full native endofunctors
requires that common bound. This is a stated specialization, not an implicit
identification of the independent levels of the native Applicative theory.
Supporting unequal levels through raised values or a relative presentation
would be a separate construction. In particular, the actual generated
small-base Day model cannot be invoked on this full native category: its
object-index size exceeds the common bound. Uniform convolution existence
therefore remains explicit input and is not claimed by this module.

This bounded bridge is an object/operation/morphism correspondence under
those hypotheses. It does not add an Applicative category or claim a new
categorical equivalence of bundled Applicatives. Strong profunctors,
coherent further connections and justified free constructions remain open.

### The ordinary profunctor prerequisite

[The ordinary interface](../../theories/Cat/Profunctor/Core.v) uses exactly the
existing mixed-variance functor bundle. `Profunctor` names a setoid-valued
functor contravariant in its input and covariant in its output; its existing
object-map coercion and `fmap` remain available. No duplicate structure/data
record or extra homomorphism predicate is stored. `ProfunctorCat` is the
existing functor category, with natural transformations and their specified
pointwise equality. Neither an end nor a coend is required for these types.

The shared scoped notation `dimap`, `lmap`, `rmap` reads existing functor
maps as two-sided preprocessing/postprocessing and their one-sided actions.
Functor laws prove identity, composition and respectfulness. The one-sided
natural comparisons reuse product-coordinate restrictions; their naturality
supplies interchange and the two decompositions of `dimap`. Input and output
category object/Hom/equality levels are independent of one another and of
the value carrier/equality bounds, with no order between the two value levels.

`ProfunctorReindex` precomposes opposite/product functors. Transformations
and specified inverse witnesses are right-whiskered by the existing theory.
`ProfunctorReindexF` restricts the existing horizontal-composition functor;
its arrow action agrees with right whiskering in natural equality. This
comparison is deliberately not record equality: an identity functor map
may change representatives while satisfying the specified equality law.
Ordinary naturality already gives the profunctor transformation equation.

[The Hom client](../../theories/Cat/Profunctor/Hom.v) lifts the existing `HomF`
with independently declared carrier/equality bounds. It then reindexes to
`Hom (F X) (G Y)` for two functors with a common target, using that target's
original composition. The bounds must contain the actual Hom carrier and
Hom equality levels; no bound on indexing objects, ambient equality/carrier
identification, global choice or resizing is asserted. This interface is
intended for the later computation-Hom client without assuming strength.

This independent prerequisite does not compose profunctors or provide
monoidal strength, promonads or the Arrow monoid characterization. Those
clients follow after this foundation is integrated, with their own actual
coend/existence/strength hypotheses. Conditional free constructions remain
later work in the agreed semantic endpoint.

### Left-context profunctor strength

[The strength interface](../../theories/Cat/Profunctor/Strength.v) adds chosen
left-context action to a supplied profunctor over a named monoidal category.
For each context, it stores an ordinary natural transformation into
`ProfunctorContext`, which reuses the existing reindexing along the same
`BinoidalLF` at both ends. Naturality in input and output is inherited
from that transformation, rather than stored again as separate laws.
The derived `pstrength` notation is confined to `profunctor_scope`.

Changing the context satisfies a dinaturality equation: ordinary substitution
can act at either end of the computation. It does not require the context
map to be invertible. The unit and associator equations use the original
monoidal boundaries and designated equality; no native equality of objects,
functions or law records is required. This left-context convention matches
the existing computational Arrow context. It does not assume symmetry,
cartesian products or effect interchange, and it does not choose a strength
from an arbitrary ordinary profunctor.

[The Hom client](../../theories/Cat/Profunctor/HomStrength.v) explicitly selects
the original fixed-context functor's arrow map as Hom strength.
`HomProfunctorMapN`, added to the [Hom module](../../theories/Cat/Profunctor/Hom.v),
first makes any supplied functor's lifted Hom map a natural transformation.
The strength reuses this naturality; coherence reuses monoidal interchange
and the existing left-unitor/associator naturality. Its lifted respectful
components preserve independent value and equality bounds as well as the
context functor's auxiliary law bounds. Only the actual Hom carrier and
equality levels must fit their respective value bounds; object indices
need not fit either bound. These are explicit constructions, with no chosen
model instance registered by importing either module.

Neither module assumes or constructs a coend. Composition of profunctors,
strength on that composition, strong promonads and the Arrow-monoid comparison
remain subsequent stages, with their actual existence and size assumptions.
The general conditional free constructions also remain open.

### Ordinary profunctor composition through specified coends

[Composition](../../theories/Cat/Profunctor/Compose.v) takes a profunctor `P`
from `C` to `D`, followed by `Q` from `D` to `E`. The composite is written
`Q ∘Pr P` in `profunctor_scope`. Its kernel at outer boundaries `X,Z` has
values `P(X,B)` paired with `Q(A,Z)` at the middle indices `A,B`.
The value-pair order is always the execution order: `P` first, then `Q`.
Existing one-sided restrictions, whiskering and pointwise setoid products
supply the kernel and its outer-boundary natural transformations.

`HasProfunctorComp` chooses coends only for this kernel family. The resulting
mixed-variance functor uses existing coend maps and their equality, identity
and composition laws. Carrier and equality value levels remain independent;
there is no implicit size order or completeness assumption. No strength is
needed to compose ordinary profunctors.

[Generators and descent](../../theories/Cat/Profunctor/ComposeUniversal.v) retain
the original diagonal coend injections. Intermediate arrows move from the
output action on `P` to the input action on `Q` by the original cowedge
law; identity actions are removed using the existing functor laws.
A fixed-boundary injection, gluing, descent, computation, uniqueness and
reinsertion require only one selected coend. An outer-boundary map requires
only its two endpoint coends; the full composite's dimap specializes that
same equation. These wrappers keep the original transparent universal maps
and specified equality, with no separate quotient or dual construction.

[The explicit setoid model](../../theories/Instance/Set/ProfunctorComp.v) reuses
`SetCat_Coend`. Its sufficient bounds concern the middle category alone:
its object and Hom-carrier levels fit the value carrier, which fits the
value-equality level. The middle Hom-equality level remains independent;
this kernel carries no Hom weight. Source and target categories need not
fit those value bounds. The model is explicitly enabled and does not assert
fixed-size full-setoid self-indexing or resizing. Its sufficient bounds are
not extra requirements on a separately supplied abstract coend.

Composition on input transformations, associators/unitors and their coherence,
strength on the composite, strong promonads/Arrow monoids and the conditional
free constructions remain subsequent independent stages.

### Input transformations and the profunctor composition bifunctor

[Natural maps](../../theories/Cat/Profunctor/ComposeMap.v) transform the two
kernel value coordinates by the supplied ordinary natural transformations.
Their order is `P` then `Q`, while the composite and bifunctor arguments are
written `Q` after `P`. The original naturality equations give the commuting
square with outer boundary changes. The induced transformation of composites
uses the existing coend map, its specified equality, and its identity and
composition laws; no second universal-property argument is introduced.

A transformation between two composites requires only those two endpoint
composition choices. Its chosen inverse is obtained by the same construction
on the supplied inverse input transformations; both inverse laws use `NatEq`.
At a fixed outer boundary, generator computation and compatibility with
descent require only the two individual kernel coends. These interfaces do
not need a uniform family of choices or any size order between the value
carrier and equality levels, or between those levels and category indices.

`ProfunctorCompF` packages the bifunctor on the existing profunctor categories
only after receiving a choice for every input pair explicitly. No global
instance chooses such a family. The explicit setoid existence model keeps
its previously stated middle-category bounds; the bifunctor does not assert
fixed-size full-setoid self-indexing. Associators/unitors, their coherence,
composite strength, strong promonad–Arrow comparisons and conditional free
constructions remain separate subsequent stages.

### The co-Yoneda prerequisite for Hom composition units

[Co-Yoneda](../../theories/Cat/Coend/Yoneda.v) treats any covariant setoid-valued
functor. Its kernel pairs a covariant value with a raised contravariant Hom
weight. Evaluation on the original value at the target is a universal
cowedge: every balanced operation factors uniquely through its component at
the identity. The proof uses the original cowedge equation and functor laws,
with Type-valued uniqueness and the existing opposite-end coend interface.

`CoyonedaCoend` explicitly enables only this particular coend on that original
value; import installs no chosen instance. Object indices need not fit the
value bounds, and the carrier/equality bounds have no required ordering.
The actual Hom carrier and equality levels must fit their respective value
bounds independently. The kernel reads the supplied functor's operations
and retains its independent auxiliary law bounds, reusing the original
functor laws and Hom composition laws coordinatewise. This direct
representable construction does not invoke
the general setoid coend model, its index-size sufficient conditions, resizing
or fixed-size full-setoid self-indexing.

With any independently supplied coend of the same kernel, the original
coend mediator evaluates generators and identity insertion gives its inverse.
Both complete inverse laws use specified equality. Comparisons commute with
input natural transformations and changes of the target object, requiring
only their two endpoint coends. Hom-composition unitors, associators and
coherence, composite strength and the later strong-promonad/Arrow/free
constructions remain dependent stages; this module does not claim them.

### The left Hom unit for profunctor composition

[The left unit](../../theories/Cat/Profunctor/LeftUnit.v) composes a profunctor
from C to D with the raised Hom profunctor of D. Its actual composition
kernel is naturally isomorphic to the covariant co-Yoneda kernel of the
output fibre. The comparison retains the value and represented arrow,
rewrapping lifts at their respective bounds and removing Hom's identity
postcomposition in specified equality. It identifies no functor records.

The co-Yoneda mediator and uniqueness witness directly give the Hom kernel's
universal evaluation cowedge. `ProfunctorLeftUnitComp` explicitly selects
this composition on the original P values. Only D's Hom carrier and equality
must fit the corresponding independent value bounds; no object-index bound,
order between the value bounds or general setoid coend model is required.
Import does not choose a model globally.

For any independently supplied fixed-boundary coend, evaluation and identity
insertion are transparent inverses on the whole coend. A supplied composition
family assembles the natural unitor and its inverse. Evaluation also commutes
with transformations of P; its fixed-boundary square needs only the two
individual coends. The inverse square is inherited from the general
isomorphism-square theorem. The right Hom unit still requires the opposite
and index/factor reorientation stage; associativity, coherence, composite
strength and the strong-promonad/Arrow/free constructions remain later work.

### Reversing end/coend indices without reversing values

[The index adapter](../../theories/Cat/Functor/IndexReversal.v) exchanges the
mixed-variance coordinates and views the index as its opposite, retaining the
codomain. It reuses product projection/pairing and the double-opposite
adapter; transformations retain their direction, components and computed
inverses. It differs from `BifunctorOpF`, which reverses the codomain too.

[The end wrappers](../../theories/Cat/End/IndexReversal.v) retain each wedge's
apex and exact legs, reading its commuting equation in reverse. The existing
universal end witness receives the backward or forward test-wedge wrapper;
no new existence or uniqueness proof is required. `EndIndexOp` and
`EndIndexUnop` explicitly retain the chosen apex and this same factorization
function. Their mediator laws use the original mediator on the wrapped test
wedge, without equating records or law witnesses.

[The coend wrappers](../../theories/Cat/Coend/IndexReversal.v) read those same
end witnesses in the opposite codomain, rebundling the stored wedge
presentation rather than identifying the functor records. Both directions
retain the supplied apex, injections and descent function. No second dual
universal-property proof, global instance, choice or notation is introduced.
The constructions impose no new object, Hom or value-size ordering. Existing
co-Yoneda or generated setoid models still require their own actual bounds.

This independently reusable prerequisite supports the planned right Hom unit:
apply the covariant co-Yoneda theory on the opposite category, then explicitly
reorient indices and exchange the value/Hom factors with their lift wrappers.
That dependent unit, its natural comparisons and later associativity,
coherence, composite strength and free constructions are not claimed here.

### The right Hom unit from opposite co-Yoneda

[The right unit](../../theories/Cat/Profunctor/RightUnit.v) places the raised
Hom profunctor of C before P from C to D. Reverse the original composition
kernel's index, then exchange its Hom/value factors and rewrap the represented
arrow's lift. This gives a natural isomorphism to the existing covariant
co-Yoneda kernel for P's contravariant fibre on C's opposite category.
The original mediator and uniqueness witness apply there; index-unop reads
them back on the original kernel. No contravariant co-Yoneda or dual universal
property is proved independently.

`ProfunctorRightUnitComp` explicitly chooses this special composition on the
original P values. The actual requirements are C Hom carrier ≤ value carrier
and C Hom equality ≤ value equality, without ordering the two value bounds.
No object-index bound or bound on D's Hom/equality is added; import selects
no composition model globally.

For any supplied single kernel coend, its original mediator evaluates an
input arrow by preprocessing, and its original injection inserts the identity.
The two maps are transparent inverses on the whole coend. A supplied family
assembles a natural right unitor and its computed inverse. Outer-boundary
naturality uses the existing Hom and single-coordinate action laws; input
naturality at one boundary needs only the two endpoint coends. Its inverse
square is the existing general inverse-isomorphism-square theorem.

Both Hom units are now available under their respective actual bounds and
supplied choices. Associativity, triangle/pentagon coherence, composite
strength and the strong-promonad/Arrow/free constructions remain separate
stages; these units alone do not assert a monoidal profunctor category.

### Endoprofunctor composition as a monoidal category

[The monoidal assembly](../../theories/Cat/Profunctor/Monoidal.v) retains the
existing composition bifunctor's objects, input maps and functor laws, with its
usual order: the left factor follows the right
factor, while generated pairs retain execution order. Fix a uniform family of
chosen kernel coends. The tensor uses those same choices, and its associator
is the inverse of the previously constructed ordered reassociation.

The inverse input square supplies natural associativity. The accepted
pentagon is reversed by the general `iso_pentagon_inv`; the existing
composition-map properness laws compare its whiskered inverses with the native
inverse input maps. The Hom units retain their original identity-insertion
inverses. Moving the old associator across the accepted triangle gives the
triangle for the inverse associator. `BifctMonoidal` supplies interchange
and the remaining separate naturality, without re-proving coend universality.

Associativity and its pentagon need no Hom-unit bounds. Full assembly requires
the base Hom carrier and equality to fit the corresponding independent value
bounds. It adds no object-index bound or ordering between those value bounds.
Uniform composition existence is still explicit input; importing the module
does not select a global model or assert fixed-size full-setoid self-indexed
coends. The reconstructed tensor map agrees with the supplied composition map
by natural equality, and identity components give their tensor-functor
comparison. No equality of functor records or law witnesses is required.

This packages ordinary endoprofunctor composition. Composite strength, its
coherent compatibility, the strong-promonad/Arrow characterization and
conditional free constructions remain separate stages.

### Strength on a supplied profunctor composite

[Composite strength](../../theories/Cat/Profunctor/ComposeStrength.v) applies the
two supplied strengths to a generating pair, then inserts at the intermediate
object extended by the same left context. Single-sided naturality is derived
from the original strength transformation. It turns the balance equation into
original coend gluing, so the existing balanced-cowedge constructor and
transparent mediator supply descent and its generating equation. The original
coend extensionality gives uniqueness on the entire coend.

Balanced legs need only the target kernel coend. Descent and its uniqueness
need that target and the original source kernel coend, with independent
choices. Packaging a natural transformation and `ProfCompStrength` uses only
the supplied composition family for the two fixed profunctors. Endpoint
naturality follows on generators. Context dinaturality, including
noninvertible substitutions, and the unit/associativity strength equations
move the middle context map, unitor or associator between factors by gluing.
No separate universal-property proof is introduced.

The base is monoidal; symmetry, cartesian operations and tensor preservation
of coends are unnecessary. Value carrier/equality levels remain independent;
no object-index or Hom-size bound is added to the abstract construction.
Existence stays explicit: the generated setoid model retains its actual size
conditions, while special Hom coends can be supplied directly by co-Yoneda.
No import selects a global strength/coend model or asserts fixed-size full
SetCat self-indexed coends. Compatibility of strength-preserving input maps
and the composition unitors/associator, the strong-profunctor monoidal
packaging, strong-promonad/Arrow comparison and conditional free constructions
remain subsequent stages.

### Strength-preserving transformations and their category

[Strength-preserving natural transformations](../../theories/Cat/Profunctor/StrengthNatural.v)
commute with extending both profunctor ends by the same left context. The
Type-valued predicate is placed on the original transformation, whose endpoint
naturality is already supplied. Natural equality transports preservation;
identity and vertical composition preserve it. A specified natural inverse
preserves strength by the existing `iso_square_inv` on each context square,
without a new naturality or inverse-universality argument.

`StrongProf` stores one underlying functor and one strength relative to the
named ambient monoidal structure. The functor is the sole coercion view;
`hasProfStrength` exposes that same stored evidence. `StrongProfCat` uses subset
hom-setoids of the original natural transformations: equality does not compare
preservation witnesses. Its faithful forgetful functor keeps the original
functor and component maps, and `StrongProfIso` lifts a supplied natural
isomorphism with exactly its chosen forward and inverse maps.

This category requires no coends, symmetry, cartesian operations or bounds on
base objects/Homs relative to value universes. Carrier and equality bounds
remain independent. It does not yet lift profunctor composition to a strong
bifunctor or establish strength compatibility of its unitors/associator.
Those constructions, strong monoidal packaging, the strong-promonad/Arrow
comparison and conditional free constructions remain dependent stages.

### Strong composition maps and bifunctor

[Strong composition](../../theories/Cat/Profunctor/StrongCompose.v) lifts the
original coend input map when both transformations preserve their supplied
strengths. At a fixed context and outer boundary, the square needs only four
individual coends: input and output choices before and after context extension.
On generators it is exactly the pair of input preservation equations; original
coend extensionality extends it to the full source coend. No tensor preservation
of coends, symmetry, cartesian operation or additional base-size bound is used.

Two supplied composition families suffice for `StrongProfCompMap` and
`StrongProfCompIso`. The latter lifts the original chosen coend isomorphism
with its original inverse. `StrongProfComp` stores that same composite functor
and its strength; subset arrow equality compares only underlying natural
transformations. The new respectfulness law therefore ignores preservation
witnesses while retaining them as Type-valued data.

`StrongProfCompF` requires uniform composition choices only for pairs of
strong profunctors. It reuses the old map identity/composition laws, with the
ordinary left-after-right order; forgetting its arrows gives the old input
map in designated natural equality. Carrier and equality levels remain
independent. Importing the module chooses no global coend model, and the
construction does not assert fixed-size full-SetCat self-indexed existence.
Strength compatibility of the unitors and associator, strong monoidal
packaging, the strong-promonad/Arrow comparison and conditional free
constructions remain subsequent stages.
