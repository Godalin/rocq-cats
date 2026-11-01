# Working on Rocq-Cats

A constructive category theory learning library. Follow [issue #1](https://github.com/Godalin/rocq-cats/issues/1):
prefer small reusable components, readable mathematics, and incremental changes.
CCC/STLC, ETCS, and dependent type theory are independent directions.

## Mathematical design

- Preserve Type-valued relations and computational witnesses; do not replace
  them with Prop-only interfaces or introduce unproved assumptions.
- Sets mean setoids; strict laws use their specified equality. Rocq's `eq`
  is one concrete choice (e.g. for `nat`). Use categorical/setoid equality and
  prove operations respectful (`Proper`). Compare functors by natural isomorphism.
  Do not require equality of functions or proof fields when the mathematical
  interface only needs equivalence.
- Families require coherent transport. Distinguish strict equations from laws
  up to equivalence/isomorphism, and invertible higher cells from strict equality.
  Specify the coherence needed by each construction.
- Keep cell and equivalence-witness universes independent; put size bounds for
  laws in auxiliary universes. Check inferred types at distinct levels.
- Separate candidate universal properties (`is_*`) from chosen structures
  (`Has*`); use the weakest sufficient assumptions. Chosen model structures
  must be explicitly enabled, not registered globally by import.
- Bundle category-like data and laws in one `Class`, without a staging `*Data`
  record. Keep derived operations separate.

## Code and naming

- Follow nearby notation, universe polymorphism, and typeclass conventions.
  Design shared, exported notation alongside new operations; avoid local
  notation aliases. Prefer UTF-8 and pair/projection notation. Check scopes,
  precedence, and chaining.
- Use `Program Definition`/`Program Instance`/`Program Canonical` with named
  record fields for data, then explicit `Next Obligation` proofs. The default
  `cats_obligation` only introduces parameters and runs `cbn`; do not restore
  automatic destruction of dependent witnesses. For staged proofs, use named
  fields with `refine`, avoiding positional constructors.
- Keep computational witnesses transparent (`Defined`), especially inverse
  maps, transports, and universal mediators. Never finish with `Admitted`,
  `Admit Obligations`, or new axioms. Make any additional assumptions explicit.
- Structures/constructions use capitalized names; helpers use `snake_case`.
  Use `is_*` for predicates, `Is*` for property classes, `Has*` for chosen
  structures, `*Eq` for equivalences, and `<subject>_<Class>` for instances.
- Preserve abbreviations: `S` = setoid, `C` = category, `F` = functor,
  `N` = natural transformation, `r`/`resp` = respectful, `v` = vertical.
  `_resp` names respectful maps; `_proper` names preservation laws.
- Prefix laws by their mathematical subject, not `axiom_`. Reuse descriptive
  endings (`_id`, `_comp`, `_inv`, `_iso`, `_unique`, `_β1`, `_η`).
  `_universal` denotes the full universal property; distinguish mediator
  uniqueness from object uniqueness. Follow local spelling; update references
  together when renaming, without unnecessary compatibility aliases.

## Organization and workflow

- Foundational sets and respectful maps belong under `Set/`, without category
  dependencies. Abstract interfaces and general constructions belong with their
  theories; concrete models belong under `Instance/<base>/`. Keep `Instance.Set.Core`
  dependent only on `Cat.Core`; import extensions individually.
- Inspect Git status and preserve user work. When asked to save experiments,
  use a named stash including relevant untracked files, verify it, and report
  restoration instructions. Do not automatically reapply or discard it.
  Distinguish committed-baseline findings from experimental code.
- Keep related issues current after meaningful changes, commits, and CI results:
  update checklists, link evidence, and note remaining work. Distinguish
  committed tests from temporary checks; close issues once acceptance criteria
  are met.
- Tools come from the initialized Nix login environment. Check tool resolution
  and versions before diagnosing failures; do not install dependencies or
  change global shell settings to bypass an unloaded environment.
- Build with the existing VS Code task or `dune build`. Compile affected modules
  and dependents; broaden validation after interface changes. Inspect
  `Print Assumptions` for foundational proofs or suspected hidden axioms.
- Prefer general proofs and temporary checks to redundant tests. Retain tests
  only for concrete interface regressions; keep reusable mathematics in theory
  modules and routine assumption output out of compiled sources.
- Do not edit generated `_build/` files or `rocq-cats.opam` (edit `dune-project`).
  Avoid cleaning without evidence of stale artifacts. Report actual checks,
  toolchain, and remaining limitations; local success does not establish CI.
