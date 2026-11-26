# Basic CCC structure and hom equations

The first structural milestone of [#23](https://github.com/Godalin/rocq-cats/issues/23)
connects exponential identities, their hom-setoid computations, limit preservation,
cartesian closed functor composition and internal composition. The selected
[CCC interface](../../theories/Cat/CCC/Core.v) extends a chosen
[cartesian structure](../../theories/Cat/Cartesian/Core.v) by exponentials for
its inherited products. The unique underlying-view chain is
`CCC → CartCat → Cat`. Individual theorems use weaker assumptions
where possible; extracting this parent does not add hypotheses to them.

Minks packs the underlying category, terminal object, products and
exponentials in `CCC`. The exponential mixin depends on the stored products.
`CCCToCartCat` recovers the cartesian parent from the same selections.

`CCCFct` extends `CartFct` with `PreservesExp`, the invertibility of the
exponential comparison for the stored cartesian witness. Fixing its functor
exports `IsCCCF`. The generated `CCCFctToIsCCCF` and `CCCFctOfIsCCCF`
extract and reassemble that interface.
`exp_cmp` names the general exponential comparison, and `fct_exp_cmp`
is its cartesian-functor adapter. Other lowercase
functor/exponential identifier segments use `fct`/`exp`; module paths and
`HasExponential` stay unchanged.

The cartesian and CCC functor modules, product preservation and exponential
comparison now locally default to object notation. Expressions such as
`F (X × Y)` and `fmap F (f × g)` coexist without `%ob` or `%hom`; the latter
uses the existing hom argument scope of `fmap`. These local settings do not
change the importing module's default. See the
[object/morphism notation convention](../development/CodeStyle.md#object-and-morphism-products).

## CCC modules and the category of CCCs

The theory is organized by mathematical subject:

| Module | Responsibility |
| --- | --- |
| [CCC/Core.v](../../theories/Cat/CCC/Core.v) | The complete CCC record and inherited choices |
| [CCC/Functor.v](../../theories/Cat/CCC/Functor.v) | `IsCCCF`, `CCCFct`, its parent view `CCCFctToCartFct`, identity and composition |
| [CCC/Category.v](../../theories/Cat/CCC/Category.v) | `CCCCat`, hom equality and the forgetful functor |
| [Functor/ExponentialComparison.v](../../theories/Cat/Functor/ExponentialComparison.v) | General comparison, evaluation and currying, with weaker hypotheses |

`CCCCat` has complete `CCC` bundles as objects and `CCCFct C D` as
arrows. `CCCFctEq` compares only their underlying functors by a Type-valued
natural isomorphism. Preservation witnesses remain stored but are not
compared. Identity and composition reuse `IdCCCF` and `CompCCCF`; the
unit/associativity laws reuse the existing natural comparisons for `CompF`.
No native equality of object maps, functors or law records is required.

`CCCForgetF : Fct CCCCat CatCat` keeps the underlying category and functor.
It is faithful for the specified natural-isomorphism equality. Both its
respectfulness and `ccc_forget_faithful` retain the comparison components
and their selected inverses transparently.

At each universe instance, `CCCCat` contains CCCs at a fixed profile and
itself lives at larger bounds. This is a
universe-polymorphic family, not a type containing categories from every
universe. Both strict hom/equality size orders remain supported.
`tests/category/CCCCategory.v` exercises categorical notation and composition
rewriting, distinct terminal choices over one category, concrete forgetting
and the underlying functor at strictly larger auxiliary proof bounds.

The object-level universe checks
`Check CatCat : CatCat : CatCat : CatCat` and
`Check CCCCat : CatCat : CatCat : CatCat` now appear immediately below
their constructions
in `Cat.CatCat` and `Cat.CCC.Category`. They use the object-type coercion
and distinct universe instances; the latter does not assert a CCC structure
on CCCCat. At published checkpoint `70792e0`, local validation passed all
606 theory and 174 test modules, followed by the affected test after adding
the original two probes. The 23 temporary universe, assumption and
witness-computation checks are closed.

For self-membership within a complete cartesian structure, use
`CartCatCartCat : CartCatCartCat`; groupoids admit the analogous
`GpdGpd : GpdGpd`. See the
[constructions and universe distinction](StructureUniverses.md).

## Classical isomorphisms

[Exponential.Laws](../../theories/Cat/Exponential/Laws.v) provides:

| Isomorphism | Construction |
| --- | --- |
| `(X × Y)^A ≅ X^A × Y^A` | `exp_product_iso A X Y` |
| `(Y^A)^B ≅ Y^(A × B)` | `exp_iterated_iso A B Y` |
| `Y^1 ≅ Y` | `exp_unit_iso Y` |
| `1^A ≅ 1` | `exp_terminal_iso A` |

The product and terminal-result isomorphisms come from the existing
product–exponential adjunction and the general right-adjoint preservation
theorem. The product comparison has exponentiated projections as components;
its inverse abstracts paired evaluations. Both curry and evaluation equations
are public. Only the two unit laws need a terminal object.

The product comparison is a natural isomorphism in both result factors.
The iterated comparison is natural in the result object; its hom maps are also
natural in the context. Evaluation at the terminal argument is naturally the
identity. These statements retain explicit component arrows and inverses.

## Iterated transposition

[Exponential.Currying](../../theories/Cat/Exponential/Currying.v) supplies
`ƛ₂ f` and `g^♭₂`. Their types and equations are:

```text
f : Hom (Z × (A × B)) Y
ƛ₂ f : Hom Z ((Y^A)^B)

g : Hom Z ((Y^A)^B)
g^♭₂ : Hom (Z × (A × B)) Y

(ƛ₂ f)^♭₂ ≈ f
ƛ₂ (g^♭₂) ≈ g
(g ∘ σ)^♭₂ ≈ g^♭₂ ∘ (σ × id)
```

[Product.Transport](../../theories/Cat/Product/Transport.v) constructs the explicit
associator and the permutation `((Z × B) × A) ≅ Z × (A × B)`, with forward and
inverse naturality. This accounts for the argument order rather than treating
product objects as definitionally equal. Flattening/expanding the hom maps
are inverse, respectful and natural; their action is the iterated isomorphism.

## Equations and native hom-setoids

The following interfaces avoid unfolding universal-property witnesses during
routine calculations. All equalities are the designated setoid/hom equality.

| Interface | Use |
| --- | --- |
| [`iso_cancel_l`, `iso_cancel_r`](../../theories/Cat/Isomorphism.v) | Cancel an invertible composite |
| [`iso_move_l`, `iso_move_r`](../../theories/Cat/Isomorphism.v) | Move an isomorphism across an equation |
| [`product_eq_iff`](../../theories/Cat/Product/Transport.v) | Split an equation into projection equations |
| [`exp_curry_iff`](../../theories/Cat/Exponential/Core.v) | `ƛ f ≈ g ↔ f ≈ uncurry g` |
| [`exp_curry_eq_iff`, `exp_uncurry_eq_iff`](../../theories/Cat/Exponential/Core.v) | Detect equations before/after transposition |
| [`exp_uncurry_app`](../../theories/Cat/Exponential/Core.v) | Express uncurrying by contextual application |

[ProductHom](../../theories/Instance/Set/ProductHom.v) and
[ExponentialHom](../../theories/Instance/Set/ExponentialHom.v) package the actual
respectful maps as native hom-setoid isomorphisms:

```text
HomSet Z (X × Y) ≅[SetCat] (HomSet Z X ×S HomSet Z Y)
HomSet (Z × X) Y ≅[SetCat] HomSet Z (Y^X)
HomSet Z ((Y^A)^B) ≅[SetCat] HomSet Z (Y^(A × B))
```

These interfaces use `SetCat` to express setoid isomorphisms without activating
a chosen CCC model. The general `hom_iso` in [Hom](../../theories/Instance/Set/Hom.v) changes
source and target by isomorphisms through the existing Hom bifunctor.

## Limits and functor composition

[Limit.Exponential](../../theories/Cat/Limit/Exponential.v) applies the existing
right-adjoint theorem to each specified limiting cone. Terminal, product,
equalizer and pullback preservation reuse their existing limit characterizations.
Equalizer/pullback theorems take the candidate universal property as an argument.
The source only needs chosen products and exponentials; shape sizes remain
independent of its hom carrier/equality levels.

[Functor.Cartesian](../../theories/Cat/Functor/Cartesian.v) first extends preservation
of the selected terminal/product objects to arbitrary candidates using their
universal isomorphisms. This gives `CompF_IsCartF` and the inverse-product
comparison equation. [CCC.Functor](../../theories/Cat/CCC/Functor.v) proves:

```text
comparison_(G∘F)(X,Y) ≈ comparison_G(FX,FY) ∘ G(comparison_F(X,Y))
```

Invertibility then supplies `CompF_IsCCCF`. Terminal comparison composition is
already terminal-arrow uniqueness. All chosen structures and preservation
proofs remain explicitly enabled.

## Bundled preservation

[CartFct](../../theories/Cat/Functor/Cartesian.v) stores one underlying
`Fct` and its `IsCartF` evidence for named source terminal and product
structures. No chosen target products are needed until an operation uses them.
[CCCFct](../../theories/Cat/CCC/Functor.v) adds invertibility of the canonical
exponential comparison to that same cartesian bundle. Its unique coercion chain
is `CCCFct → CartFct → Fct`; the derived `CCCFctToIsCCCF`
instance reuses the stored cartesian witnesses.

`MakeCartFct` and `CCCFctOfIsCCCF` package
existing evidence transparently. `IdCartF`, `CompCartF`, `IdCCCF`
and `CompCCCF` reuse the identity and composition theorems above. Clients can
write `F X`, `fmap F f` and apply the existing comparison/curry laws directly.
The fixed-functor interfaces remain available to general theorems and STLC
clients; constructors do not register chosen model functors globally.

## Internal hom equations

[Exponential.InternalHom](../../theories/Cat/Exponential/InternalHom.v) supplies
`idᴱ[X]` and contextual composition `g ∘ᴱ f`. Their application, context
substitution, left/right unit and associativity equations follow from
transposition. The internal arrow `internal_comp X Y Z` has type
`Hom ((Z^Y) × (Y^X)) (Z^X)`. Its associativity diagram includes the explicit
product associator; unit diagrams use the two projection unitors. Internal
identities work in any context; specializing to the terminal context gives
`1 → X^X`.

## Validation and remaining extensions

Permanent [universe/interface checks](../../tests/Universes.v) cover both hom/equality
orderings, native hom correspondences, exported notation, mixed-level CCC
functor composition and limit preservation for larger shapes. Concrete
proof-relevant setoid computations and assumption audits remain temporary.

On Rocq 9.0.1, OCaml 5.3.0 and Nix Dune 3.23.1, the full build, test and
install targets pass. Eleven additional permanent checks cover the interfaces
above. The temporary audit covers 155 declarations, all closed under the global
context. Fourteen temporary computations check the actual comparison arrows,
argument order, native hom maps and internal composition on a setoid with boolean
equality witnesses. Thirteen coqdoc pages were generated and parsed successfully.
These are local results.

The bundled-functor follow-up also passes the full build, test and install
targets with the same toolchain. Added interface, computation and universe
regressions cover inheritance, explicit selection, transparent composite
inverses and separated STLC interpretation adapters. Its seven new adapters,
identity/composition constructors and inherited instance are closed under the
global context. Strict bilingual HTML export checked 507 pages.

The independent follow-ups in #23 are transfer of chosen CCC structures across
arbitrary category equivalences and packaging self-enrichment through the general
interface of #10. The basic exponential, preservation, composition and internal
hom equations above are available without those developments.
