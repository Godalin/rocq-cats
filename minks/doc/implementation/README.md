# Minks implementation guide

## Generate from the checked signature

- Use the selected components, their dependencies and ordinary parameters.
  Apply the specified layout and ordering rules for any number of parents.
  A native parent becomes a single-field base and then follows ordinary
  inheritance.
- A rule must apply to every signature with the same distinguishing feature.
  If a group or ring example exposes a bug, fix the common rule.
- Preserve component identity through renaming and export expansion. Two
  points can share a type and have different keys. An export must select the
  same witnesses as listing its components in order.

## Use Rocq and Elpi

- Generate the Class, Record or map one would write by hand. Let Rocq
  elaborate terms in context, check conversion and infer universes. Preserve
  binder order and explicitness. Explicit header parameters survive even
  when unused; Section discharge generalizes the assumptions the declaration
  uses. Read the resulting telescope.
- Put key selection, dependency closure, ambiguity, layout, relative exports
  and registration policy in Elpi. Index module-scoped declaration metadata
  by Rocq references so module functors substitute them. Share the lookup
  between `extends`, `with` and `Minks.Inspect`.
- Add an OCaml bridge only for a missing host operation. Explain the gap and
  the behavior it preserves beside the bridge. For qualified lookup, OCaml
  reads a closed module in a protected Rocq state; Elpi interprets the
  returned signature. The caller's imports stay in scope as before.

## Check public behavior

Put usage demonstrations in `examples/` and regression checks in `tests/`.
Tests may import examples. Use `Minks.all` in both. Check that a shared field takes one constructor
argument, a qualified parent leaves short names unopened, and an ambiguous
selection fails. For Coercion, Canonical or instance registrations, check
the selected witness and projection reduction as well as the map's type.

From `minks/`, build the affected example or test, e.g.
`opam exec --switch=rocq-cats -- dune build tests/Modules.vo`.
Use `opam exec --switch=rocq-cats -- dune runtest` for cross-command changes
and check an affected Cats consumer when its interface changes. Update the
[command reference](../../README.md) for public changes and the [audit](audit.md)
for regression evidence and open obligations.
