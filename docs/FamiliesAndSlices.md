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

Substitution uses the existing total-space pullback: apply
`fam_reindex_pullback (FixedFamC A) f` from
[FamReindex](../theories/Instance/Set/FamReindex.v). Its square has vertices
`SigS X A[f]S`, `SigS Y A`, `X`, and `Y`, and its universal mediator is already
available. This requires no new choice of pullbacks.

## Natural substitution comparisons

[SliceReindex](../theories/Cat/SliceReindex.v) constructs `SliceReindexF f`
for any category with explicitly enabled chosen pullbacks. Write `A[f]C`
for its object action. Morphisms are universal mediators; `pb_β1`, `pb_β2`
and uniqueness prove their functoriality and independence from triangle
witnesses. `slice_reindex_lift_iso` compares any pullback cone with the chosen
one in the slice. Its inverse is the mediator of the supplied cone.

The natural isomorphisms `slice_reindex_id_nat_iso` and
`slice_reindex_comp_nat_iso` compare identity substitution with pullback along
the identity, and iterated pullback with pullback along a composite. The latter
uses the existing pullback-pasting property. Their family counterparts are
`fam_reindex_id_nat_iso` and `fam_reindex_comp_nat_iso` in `FamFixed`.
The identity comparison points from the identity functor to reindexing;
the composition comparison points from iterated reindexing to the composite.

[FamSliceReindex](../theories/Instance/Set/FamSliceReindex.v) uses the existing
family pullback and `slice_reindex_lift_iso` to construct
`fam_sum_reindex_nat_iso f`:

```text
FamSumF X ∘F FamReindexF f ≅N SliceReindexF f ∘F FamSumF Y.
```

This checks naturality on fiberwise maps, not only objectwise pullbacks.
`fam_sum_reindex_id` states that the sum comparison after the family identity
comparison equals the slice identity comparison. `fam_sum_reindex_comp` states
that the two paths from the sum of an iterated reindexing to the pullback along
the composite agree: either first compare the families and then take the sum
comparison, or take the two sum comparisons and then compare the pullbacks.
Both equations use the slice's underlying-map equivalence.

The chosen `SetCat_HasPullback` explicitly keeps carrier and equality levels
separate, with the same `p <= u` bound. The regression check in
[Universes](../tests/Universes.v) includes `p < u` for this instance and the
natural sum comparison. Inverse mediators and the identity/pasting universal
properties remain transparent.

The same module constructs `slice_fam_reindex_nat_iso f` in the other direction:

```text
FamReindexF f ∘F SliceFamF Y ≅N SliceFamF X ∘F SliceReindexF f.
```

Over `x`, an element `(a,r : q a ≈S f x)` is sent to the pullback point
`(x,(a,r⁻¹))`, with reflexive membership over `x`. In the inverse direction,
a point `(y,(a,s))` over an equivalent `x` keeps `a` and combines `s⁻¹`
with the image of `y ≈S x` under `f`. The specified inverse remains
computational, and neither direction compares membership proofs.

Two equations connect the sum and fiber comparisons to the existing round trips:

- `slice_fam_reindex_fiber_total`: either compare the sum first and pull back
  the slice round trip, or take the sum of the fiber comparison and then
  apply the slice round trip. Both paths give the same map in the slice.
- `slice_fam_reindex_total_fiber`: start with fibers of the sum of a reindexed
  family. Taking the fiber image of the sum comparison, the inverse fiber
  comparison, and the reindexed family round trip agrees with the direct
  family round trip. This uses transport witness independence.

The full unit/associativity coherence of the indexed equivalence remains
follow-up work. These results do not assert a
strict CwF or the global fibred equivalence proposed in
[issue #13](https://github.com/Godalin/rocq-cats/issues/13).
