# Coherent families and slices

[Issue #5](https://github.com/Godalin/rocq-cats/issues/5) compares two
presentations of dependent data over a setoid `X`:

```text
FamSCat X ≃C (SetCat /C X).
```

## The two categories

[Slice](../theories/Cat/Slice.v) is defined for any category `C`. An object
of `C /C X` is an arrow `p : E → X`. A morphism from `p` to `q : D → X`
consists of `h : E → D` and a witness `q ∘ h ≈ p`. Morphism equivalence uses
the original `HomEq` on `h`, without comparing the triangle witnesses.
`SliceDomF` forgets the projection to `X`.

[FamFixed](../theories/Instance/Set/FamFixed.v) defines `FamSCat X`. Its
objects are the existing coherent families `FamS X`. A map `A →Fam B` is
a family of respectful maps `φ_x : A x →r B x` commuting with transport.
The relation `φ ≈Fam ψ` compares their values pointwise. `FamFixedF X`
maps this data into the existing category of all families, using the
identity base map. `FamReindexF f` extends substitution to these fiberwise maps.

## The equivalence

[FamSlice](../theories/Instance/Set/FamSlice.v) provides both functors:

- `FamSumF X` sends `A` to its total-space projection `SigS X A → X`, and
  sends `φ` to `(x,a) ↦ (x,φ_x a)`. Its map on total spaces reuses the
  existing `fam_total_resp` through `fam_map_to_fam`.
- `SliceFamF X` sends `p : E → X` to `FiberFamS p`. Over `x`, its elements
  are pairs `(e,r)` with `r : p e ≈S x`. A commuting triangle maps the first
  coordinate and composes its triangle witness with `r`.

Both round trips have specified natural isomorphisms:

- `fam_fiber_total_nat_iso`: taking fibers and then their total space
  recovers `E`. The component forgets the fiber index and membership witness;
  its inverse sends `e` to `(p e,(e,refl))`. The inverse equations reuse
  `fiber_total_iso`, whose data is transparent.
- `fam_total_fiber_nat_iso`: taking the total space and then its fibers
  recovers `A`. An element over `x` can have the form `((y,a),r)` with
  `r : y ≈S x`; its image is **`transpS A r a`**, not simply `a`.
  Its inverse inserts `((x,a),refl)`. Naturality uses transport coherence
  and witness independence.

`fam_slice_equiv X` bundles these functors and comparisons. No equality of
family records, functions, or witness data is required.

## Sizes and substitution

The equivalence explicitly names `X : SetC@{u p}`. In this fixed-size
presentation, fiber carriers also live in `Type@{u}` and their equivalences
in `Type@{p}`. The construction requires `p <= u`: a fiber contains a base
equivalence witness as part of its carrier. The levels need not be equal;
`p < u` is supported. Larger auxiliary universes hold category records and
law witnesses. No resizing or choice is used. If base equality lives above
the chosen carrier universe, a larger presentation of the base is needed
before applying this equivalence.

The general slice construction does not impose that bound on its original
category's morphism equivalence.

Substitution agrees with the existing total-space pullback: apply
`fam_reindex_pullback (FixedFamC A) f` from
[FamReindex](../theories/Instance/Set/FamReindex.v). Its square has vertices
`SigS X A[f]S`, `SigS Y A`, `X`, and `Y`, and its universal mediator is already
available. This requires no new choice of pullbacks. Identity/composition
comparisons remain isomorphisms; the equivalence does not assert a strict CwF
or the global fibred equivalence proposed in
[issue #13](https://github.com/Godalin/rocq-cats/issues/13).
