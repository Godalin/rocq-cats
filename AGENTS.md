# Working on Rocq-Cats

## Purpose and scope

This is a personal learning and experimentation library for constructive category
theory in Rocq. Follow the design principles in
[issue #1](https://github.com/Godalin/rocq-cats/issues/1). Develop small, reusable
categorical components and assemble semantic models from them. CCC/STLC, ETCS,
and CwF/dependent type theory are independent directions; none is the mandatory
foundation of the whole library. Prefer readable mathematics and incremental
changes over framework machinery or repository-wide rewrites.

## Repository map

- `theories/Meta.v`: Type-valued logic, equivalence relations, uniqueness, and
  shared proof helpers.
- `theories/Cat/Core.v`: categories, morphism equivalence, duality, products,
  terminal/initial objects, and exponentials.
- `theories/Cat/Set.v`: setoids, respectful functions, `SetCat`, and dependent
  set constructions.
- `theories/Cat/SetPullback.v`: constructive chosen pullbacks for `SetCat`.
- Other `theories/Cat/` modules: functors, natural transformations, presheaves,
  pullbacks, morphism properties, and CCC structure.
- `theories/ETCS/`: subobjects, classifiers, natural numbers, and ETCS axioms.
- `dune-project` and `theories/dune`: build configuration; the logical namespace
  is `Cats`. `rocq-cats.opam` is generated: edit `dune-project` instead.

## Mathematical conventions

- Preserve constructive witness data. The library uses Type-valued relations
  and `sigT` witnesses; do not silently replace them with Prop-only interfaces.
- Use each category's `HomEq` and prove operations respect it (`Proper`). In
  setoid models, use pointwise setoid equivalence where appropriate rather than
  requiring equality of functions.
- Do not introduce functional extensionality, UIP, proof irrelevance, choice,
  classical axioms, or strictification without making the assumption explicit
  and explaining why it is needed. Check generated proof assumptions when
  dependent elimination or automation may introduce them.
- Distinguish `is_*` universal properties of specific candidates from `Has*`
  chosen constructions. General theorems should use the weakest sufficient
  assumptions. Prefer a shared universal-property definition, but evaluate
  proof usability and computation on one interface before broader migration.
- Treat equality and coherence as mathematical design decisions. Functor
  comparison must account for morphism action and dependent transports.
  Pointwise equality of natural-transformation components does not require
  equality of their naturality proofs. Setoid-indexed families need coherent
  transport; arbitrary isomorphisms between fibers are insufficient. Distinguish
  strict substitution equations from laws up to equivalence or isomorphism.
- Follow the local notation, universe-polymorphic style, typeclass conventions,
  and short proof patterns. Do not add `Admitted`, `Admit Obligations`, or axioms
  as completed fixes. Existing holes are audit findings, not proof validation.

## Working tree and experiments

- Inspect Git status before edits and preserve user work. Uncommitted files may
  be experiments, not the intended baseline for an audit.
- When asked to save experiments, use a named stash including relevant
  untracked files, verify the stash contents, and report how to restore it.
  Keep task deliverables outside that stash. Do not discard or automatically
  reapply experiments over subsequent changes.
- Distinguish findings about the committed baseline from experimental code.
  Report concrete mathematical consequences with file/line references. Do not
  turn an audit request into an unsolicited mass refactor.

## Environment and validation

- Development tools are available through the user's Nix environment. Check
  tool resolution in a properly initialized login shell; do not assume the
  macOS system Git/Xcode toolchain is usable. A sandbox may block shell
  initialization or Nix paths; use the normal approval mechanism when needed.
- Do not change global shell settings or install dependencies merely to work
  around an environment that has not been loaded. Check available Rocq/Coq,
  Stdlib, and Dune versions before diagnosing project failures.
- The project requires Dune >= 3.17 and Rocq/Stdlib >= 9.0. CI covers Rocq 9.0,
  9.1, latest, and dev. Local validation only establishes results for the local
  toolchain.
- Use the existing VS Code build task when applicable; the underlying build is
  `dune build`. For proof changes, compile the affected modules and their
  dependents. Run appropriate broader checks after interface changes.
- For foundational proofs or suspected hidden axioms, inspect
  `Print Assumptions` on the relevant declarations. A successful build alone
  does not establish that a theorem is free of admitted assumptions.
- Keep this theory library lean: prefer general proofs, compilation, and
  targeted assumption checks over tests that merely restate proved laws.
- Keep permanent tests only when they catch a concrete interface regression.
  Put reusable mathematical constructions in theory modules; use temporary
  checks for one-off counterexamples and exploratory instances. Do not leave
  routine `Print Assumptions` output in compiled library or test files.
- Do not edit generated `_build/` files. Avoid cleaning build artifacts unless
  needed to resolve a demonstrated stale-build problem.
- State what was actually checked, the toolchain used, and any remaining
  limitations. Keep validation proportional to the change.
