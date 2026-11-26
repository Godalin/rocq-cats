# Reverse canonical packing experiments

The two fixtures enable reverse packers locally. Minks still generates the
component instances and cuts for its relative classes as usual.
[Plugin fixture](../../tests/CanonicalPacking.v) ·
[Cats fixture](../../../tests/category/CanonicalMonoidal.v)

## Search rules under comparison

1. **Relative class.** The existing cut forbids a field projection of an
   export immediately followed by that export's constructor.
2. **Selected parent.** Register a canonical value constructed from a fixed
   packed parent and its missing class arguments. For example, `M : Monoid`
   can be used as a `Group` when `IsGroup M` can be found. The class can
   itself be assembled from the inverse of those exact monoid choices.
3. **Bare carrier.** When a reverse packer for structure S asks for interface
   E, also cut the adjacent steps `p MakeE` anywhere in the typeclass trace,
   for each registered component projection or extraction instance p from S.
   In the group fixture this includes `Group_hasInverse MakeHasGroup`. The
   canonical packer runs during unification; its name does not appear between
   these two hints. Apply the rule independently to each enabled packer.
4. **Source guard (alternative).** In the one-field fixture, replace both
   packed projection instances with hints that recognize the carrier of an
   already selected pack containing no unresolved variables. This also
   changes which concrete models search can discover.

### Why the bare carrier needs a separate test

With `A : Type` and `HasMonoid A`, searching for `HasGroup A` tries
`MakeHasGroup`. For its missing inverse, `Group_hasInverse` asks unification
to find a group over A. The reverse canonical packer now requests the original
`HasGroup A` again. The relative-class cut mentions `HasGroup_hasInverse`;
the trace here uses the packed projection `Group_hasInverse`.

| Local registration or control | Goal and evidence | Observed result |
| --- | --- | --- |
| Component rules alone, no reverse canonical | Group interface from monoid interface, inverse missing | Search fails |
| Reverse from bare A, only the existing class cuts | Same goal via a hole or explicit typeclass search; also `Group := A` | Each hits a two-second timeout |
| Additionally require a known input with `Hint Mode HasGroup +` | Same interface goal on rigid A | Still times out |
| Cut `Group_hasInverse MakeHasGroup` | Same missing inverse | Search fails |
| Both monoid and group reverse packers, only the group cuts | No evidence at A | Monoid class and pack time out; group class and pack fail |
| Both packers with both sets of cuts | Same four goals; also missing point, equivalence, unknown index or empty ground carrier | Search fails |
| A user registers a second name for the inverse projection, with the group cuts in place | Monoid interface at A, inverse missing | Times out again; cutting the new hint followed by `MakeHasGroup` restores failure |
| Ban every repeated occurrence of the same constructor | A supplied leaf lifts twice along product indices | Valid nested pack is lost; adjacent cuts preserve it |

For the single-group controls, import `MinksExamples.Algebra` and run:

```coq
Section Control.
#[local] Canonical group_on_type (A : Type) `{G : !HasGroup A}
  : Group := GroupOfHasGroup A G.
(* Vary the hints here. *)
Context (A : Type) `{H : !HasMonoid A}.
Timeout 2 Definition probe : HasGroup A := _.
End Control.
```

Use `Set Typeclasses Debug` and `Fail typeclasses eauto 4` on the same goal
for a bounded trace. To reproduce the wrapper bypass, add the original group
cut and register `forwarded_inverse` as in `BareCarrier.ForwardedProjection`,
initially omitting the cut on that new name. The intentional timeouts are
manual controls. The build runs the corresponding `Timeout 3 Fail` checks:
a timeout of the outer command fails the test.

## Behavioral comparisons

| Available evidence | What works | What is rejected or distinguished |
| --- | --- | --- |
| Fixed monoid | Its relative group interface or selected inverse supplies a group; explicit packing can choose another inverse | No inverse; a carrier-relative group with unrelated monoid choices |
| Carrier with monoid interface | Packs a monoid. Adding its inverse packs a group with the same parent. A supplied group class also supplies the weaker monoid class | Missing inverse; passing the class value itself as a packed group |
| Packed group | Its original extraction and field projections still reduce to the stored choices | Two inverse instances at a bare carrier are resolved by ordinary local instance order; the explicit packer selects the alternate witness |
| BCD or BCE parent | Adding the matching E or D gives BCDE; both results on shared B and C agree by conversion | Missing evidence or an interface indexed by different B and C |
| Two candidates for each dependent law at a bare carrier | Class assembly backtracks to the common pair; reverse packing gives exactly the same B, C, D and E | Each smaller interface exists but the diagonal and off-diagonal pairs are disjoint; both joint class and pack fail |
| One full BCDE interface | Reconstituting BCD from its class, then completing the parent, recovers the original four components | With only the ordinary class registrations the cast from BCD to BCDE fails |
| BC grandparent | Both explicitly typed intermediate routes agree. A separate flat canonical value enables the direct cast in isolation | Registering just the adjacent steps does not enable the direct cast. A nested ancestor packer collides with existing projection keys |
| Two independent point keys | A supplied relative class preserves both points | A single point cannot fill both keys |
| Recursive product indices | Uses the same constructor twice with a selected leaf | Missing leaf fails |
| A registered concrete model | Ordinary extraction can find it from its bare carrier | The selected-source guard loses that use, but retains projections from a supplied pack and its parent view |
| A real monoidal or symmetric premonoidal category | Symmetry and its two laws complete the first parent; interchange completes the second. Starting from one symmetric interface, the two packed results agree by conversion and can be used with `MonoidCat` | Missing unit coherence, missing interchange, or symmetry chosen for an unrelated tensor |

The selected-parent experiment needs only the existing class cuts in these
fixtures. Bare-carrier completion has a different search footprint. Cuts on
generated hints can be bypassed by a separately registered projection, so
these cases give regression evidence for the tested registrations, not a
termination theorem for arbitrary hint databases.
