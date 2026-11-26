# Development checks and testing

Use the existing `rocq-cats` opam switch: Rocq 9.3.0, Stdlib 9.2.0 and
Dune 3.23.1. Validation grows with the change's semantic impact, rather than
running the entire repository after every edit. All commands below perform
ordinary proof checking; none enables `vos` or skips obligations.

## Toolchain

Local development and both CI jobs (Linux x86-64 and macOS 26 arm64) use
the OCaml compiler and opam build dependencies in
[the toolchain lock](../../tools/ci/toolchain.lock). From the repository root,
install these versions in the project switch and verify the result.
Stop builds and language servers before updating a shared switch.
Rocq and Stdlib have independent release versions; the package bound uses
`rocq-core` because `rocq-prover` is a metapackage.

```sh
xargs opam install --yes --switch=rocq-cats < tools/ci/toolchain.lock
sh tools/ci/toolchain.sh --switch=rocq-cats | diff -u tools/ci/toolchain.lock -
```

After a deliberate toolchain upgrade, regenerate the lock with
`sh tools/ci/toolchain.sh --switch=rocq-cats > tools/ci/toolchain.lock`
and commit it with the changes that require the upgrade.

Run all project commands through this switch, without changing the global
opam selection. For VS Code, point `vsrocq.path` at this switch's `vsrocqtop`
and install a `vsrocq-language-server` matching the VsRocq extension version.

## Check selection

| Stage | Required checks |
| --- | --- |
| Editing | Changed modules, then representative consumers and regressions relevant to the change. |
| Stable task checkpoint | Affected theory and test targets; record coverage and remaining uncertainty. A local commit alone does not require a full library or test build. |
| Broad foundation/API change | Freeze the interface, names and formatting; build the library and relevant regressions once. Use all tests when many test families are affected or the consumer boundary is uncertain. |
| Integration | Build the complete library and relevant regressions at the exact resulting candidate SHA. Renew affected checks after a rebase; reuse unchanged artifacts through Dune. |
| CI | Keep the existing complete repository, test and install checks. Documentation export remains separate from ordinary local acceptance. |

Formatting-only Rocq edits normally need only their module targets during
editing. Proof-only edits also need consumers when transparency, conversion
or computation may change. A typeclass/coercion/notation/universe change
needs representative clients exercising that behavior, even if the defining
module itself compiles. Do not label selected checks as full validation.

## Commands and coverage

```sh
# One module and an explicitly selected consumer
opam exec --switch=rocq-cats -- dune build \
  theories/Cat/Core.vo theories/Cat/Functor/Core.vo

# Complete library, without test modules or exports
opam exec --switch=rocq-cats -- dune build @check-library

# All Rocq regression modules and their test aliases
opam exec --switch=rocq-cats -- dune build @check-tests

# One test file (tests/category/CoreInterfaces.v)
opam exec --switch=rocq-cats -- dune build tests/category/CoreInterfaces.vo
```

The root `tests/` theory contains the cross-library `Interfaces`,
`Computations` and `Universes` suites. Focused regressions live in directories
such as `tests/algebra`, `tests/category`, `tests/gluing`, `tests/dtt`,
`tests/relations` and `tests/stlc`. Families such as `tests/sphere` group
suites by construction. One `tests/dune` covers all subdirectories. Module paths follow the directories,
e.g. `CatsTests.category.ProductPreservation`. Use Rocq identifiers for directory
names and underscores between words.

Run the full Cats regression suite with `@check-tests`. For a focused check,
pass the test file's `.vo` path on the command line. Dune discovers modules
and imports through the Rocq theory. Keep individual `.vo` paths out of
Dune dependency lists.

`@check-library` recursively selects `theories/all`; it includes every
library module without a maintained filename list. `@check-tests` selects
`tests/runtest`, which builds `all` recursively across the test tree. Dune builds the library
dependencies needed by those tests. Tooling tests under
`tools/docs` remain covered by the existing `@runtest` CI command.
Neither alias invokes HTML/PDF exports or installation.

The existing `dune build @all @runtest @install` remains a complete
repository/package check, not the default edit loop. Library proofs themselves
are checked when their `.vo` files are built; skipping regression modules
during editing does not skip those proofs. Regression modules additionally
exercise public inference, import boundaries, universes and concrete reduction.

## Reuse and reporting

Keep each worktree's `_build` directory and reuse the initialized toolchain.
Do not clean without evidence of stale artifacts, copy generated files between
worktrees or change shared toolchains to accelerate a local check. Let Dune
track actual dependencies; directory names or a text search alone do not prove
that an API change has no consumers. A changed library module target builds
its prerequisites, not all of its reverse dependents.

Freeze broad changes before starting expensive validation. Do not add routine
formatting while that validation runs. Repeat checks for changed relevant
inputs, failures or unresolved concerns; do not repeat an unchanged full pass
at every task boundary. Integration still validates its exact candidate SHA.
Report selected targets, toolchain, results and omitted coverage. HTML/PDF
exports and install checks run when their own task or CI requires them.

Large libraries use the same separation: MathComp groups related files into
independently compilable packages, while mathlib provides CI-built artifacts
for developers to download. Rocq also supports `vos` development interfaces,
but those skip opaque proofs and require later full checking; transparent
computational witnesses in this project must remain available.
