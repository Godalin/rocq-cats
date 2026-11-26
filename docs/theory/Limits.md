# Limits, representation of cones and adjunctions

For a diagram D, a cone from X is a natural transformation from the
constant diagram at X to D. A limiting cone represents cones by arrows
into its vertex. Its universal property supplies mediating arrows and
characterizes them up to hom equality. A chosen limit also selects the
cone. [Diagrams](../../theories/Cat/Diagram/Core.v) · [Limits](../../theories/Cat/Limit/Core.v)

## Building limits

- Empty, discrete pair, cospan and parallel-arrow diagrams recover terminal
  objects, binary products, pullbacks and equalizers. Use the correspondence
  for the relevant shape to transfer the universal property.
  [Shapes](SmallCategories.md) · [Finite limits](../../theories/Cat/Limit/Finite.v)
- With the required indexed products and an equalizer, take the product
  over objects of the indexing category. Equalize the two maps to the
  product over arrows to enforce the cone equations. Terminal objects and
  binary products supply products over finite positions.
  [Indexed construction](../../theories/Cat/Limit/Construction.v) · [Finite products](../../theories/Cat/Product/Finite.v)
- For free diagrams it suffices to equalize the equations indexed by
  generating edges. Finitely generated presentations can cover shapes with
  infinitely many arrows. Transfer along a full, essentially surjective
  functor uses selected preimages and representatives to extend cones.
  [Graph limits](Graphs.md) · [Reindexing](../../theories/Cat/Limit/Reindex.v)

## Functoriality and preservation

Choosing limits of a fixed shape gives a limit functor. The natural
hom-setoid comparison between maps into a limit and cones exhibits it as
right adjoint to the diagonal. A right adjoint preserves any given limiting
cone. No choice of all limits in the target is needed for this last result.
[Diagonal adjunction](../../theories/Cat/Limit/Adjunction.v) · [Preservation](../../theories/Cat/Limit/Preservation.v) · [Dual constructions](Duality.md)

## Cone reindexing as a natural isomorphism

[Diagram.Presheaf](../../theories/Cat/Diagram/Presheaf.v) packages the existing
restriction and extension laws. `ConeS D X` is the native hom-setoid
`HomSet (ConstF J X) D` in `FctCat J C`, with `NatEq` equality. The cone presheaf
`Cone(-,D)` is the contravariant hom functor at `D`, precomposed with the
opposite diagonal functor and followed by `LiftF`. Functor laws therefore
come from the existing Hom and composition theory.

```text
ConeRestrictN Q D : Cone(-,D) ⇒ Cone(-,D ∘F Q)
cone_reindex_nat_iso HF HQ D : Cone(-,D) ≅N Cone(-,D ∘F Q)
ConeExtendN HF HQ D : Cone(-,D ∘F Q) ⇒ Cone(-,D)

cone_reindex_iso HF HQ D X
  : ↑S (ConeS D X) ≅[SetCat] ↑S (ConeS (D ∘F Q) X)
```

Restriction requires no property of `Q`; the isomorphism requires its
fullness `HF` and essential-surjectivity witness `HQ`. Its component maps are
the lifted `RestrictCone Q` and `ExtendCone HF HQ`. Inverse equations reuse
`cone_extend_restrict` and `cone_restrict_extend`. Apex naturality is
`cone_restrict_comp`; the inverse transformation's naturality is derived
by `NatIso_inv`. All comparisons use specified equality, including when
the apex morphisms have distinct equivalent representatives.

The two shape categories can have different sizes. The lifts place their
cone sets in a common ambient set category, with independent bounds for
carriers and equality witnesses. They do not resize or identify the native
shape or target universes. The actual cone components remain available
through `lower`; no new notion of cones is introduced.

For `HG : HasFiniteGen J`, `generated_cone_nat_iso D` specializes the
comparison to `generator_fct`. Equations on generating edges suffice
to build a cone on the restricted diagram by `FreeCone`, and extension gives
a cone on `D`. Here `D` is already a functor on `J`: its respectfulness
already handles the extra path equations. This does not make an arbitrary
assignment of graph edges descend to `J`.

`RestrictedLimit HF HQ D` complements `ReindexedLimit` by restricting an
already selected limit. Both retain the supplied apex and use the existing
universal-property theorems; neither promises equality of chosen records
after a round trip.
