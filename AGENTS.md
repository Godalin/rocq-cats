# Working on Rocq-Cats

A constructive category theory learning library. Follow [issue #1](https://github.com/Godalin/rocq-cats/issues/1):
prefer small reusable components, readable mathematics, and incremental changes.
CCC/STLC, ETCS, and dependent type theory are independent directions.

## Mathematical design

- For each new construction, check whether a reusable general theory applies.
  Reuse it, or extract shared arguments when useful, before specializing;
  avoid duplicating universal-property proofs in individual models.
- Define dual constructions through the original theory on opposite categories,
  then expose ordinary names, notation and laws as wrappers. Keep one underlying
  construction; do not independently rebuild its dual and prove a comparison.
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

- Write source documentation in coqdoc syntax: `(** ... *)`, `[term]` for
  code, and coqdoc headings, lists and blocks rather than Markdown. In every
  documentation item use separate comment blocks, English first and Chinese
  second. Document each definition and public lemma where practical,
  explaining its mathematical role and important assumptions; keep routine
  laws concise. Leave a blank line after every source comment before the
  following declaration or text.
- Introduce every `Section` with a bilingual coqdoc title or opening prose,
  following the [section-opening requirements](docs/ExportRequirements.md#section-openings).
  Explain its local assumptions and the theory developed next; do not rely on
  the Rocq section name to separate it from preceding code in reading editions.
- Put each required module on its own line; in grouped `Require Import` or
  `Require Export`, place the module list below the command. Keep lines near
  80 characters where practical. Wrap long declarations by parameter groups,
  indenting continued parameters four spaces. In declaration headers, always
  start the result-type `:` and definition-body `:=` on separate new lines,
  each indented two spaces, even for short declarations. Start the body on
  the same line immediately after `:=`, except that a record body beginning
  with `{ ... }` or `{| ... |}` starts on the next line.
  For `{| ... |}` literals, place the first field immediately after `{|`;
  align each following `;` and the closing `|}` with the opening `{`.
  In `Inductive` and `CoInductive` declarations with an initial constructor
  bar, write `:=| Constructor`: no space before that first `|`, one space
  after it. Use ordinary `| Constructor` syntax for subsequent branches,
  aligning their bars with the first bar in the source.
- Follow nearby notation, universe polymorphism, and typeclass conventions.
  Prefer existing public mathematical notation throughout declarations,
  construction bodies and proofs; use underlying names and explicit arguments
  where notation cannot express the needed information or resolve ambiguity.
  Design shared, exported notation alongside new operations; avoid local
  notation aliases. Prefer UTF-8 and pair/projection notation. Check scopes,
  precedence, and chaining. Use compact property/structure tags after `⦂`.
  Use `→` and `⇒` for ordinary arrows; extend them with `-` when needed,
  rather than using alternative long-arrow Unicode characters. Distinct
  symbols may express distinct meanings, such as `↣` for monomorphisms.
  Use `∏`/`∐` for indexed products/coproducts; reserve `Π` for Pi-types.
- Category extensions take a named category parameter. Declare chosen
  dependencies by name; use named `!Has*` constraints in clients. Bundle
  inherited structures with `has*`/`is*` fields and `::`.
- Expose a unique underlying function, functor or carrier with `:>` and use
  that coercion in clients. Keep competing views explicit; avoid ambiguous
  coercion paths. `::` registers inherited instances, not coercions.
- Prefer `Canonical Structure` or `Program Canonical` for canonical record
  values whose projections support parameter inference. Define interfaces
  with `Record`/`Class`; keep registrations unambiguous and retain explicit
  enabling of chosen model structures.
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

- For website and book export work, follow
  [the export requirements](docs/ExportRequirements.md). Keep future export
  presentation conventions in that file; use the documentation guide for
  commands, dependencies and implementation status.
- For mathematical illustrations, follow the
  [PDF diagram requirements](docs/ExportRequirements.md#learning-paths-and-mathematical-diagrams):
  use native TikZ-cd in coqdoc; defer webpage diagrams unless explicitly requested.
- Foundational sets and respectful maps belong under `Set/`, without category
  dependencies. Abstract interfaces and general constructions belong with their
  theories; concrete models belong under `Instance/<base>/`. Keep `Instance.Set.Core`
  dependent only on `Cat.Core`; import extensions individually.
- When a theory has a subdirectory for extensions, keep its foundational module
  in `<Theory>/Core.v`, rather than a same-name file beside the directory.
- Inspect Git status and preserve user work. When asked to save experiments,
  use a named stash including relevant untracked files, verify it, and report
  restoration instructions. Do not automatically reapply or discard it.
  Distinguish committed-baseline findings from experimental code.
- Keep related issues current after meaningful changes and commits:
  update checklists, link evidence, and note remaining work. Distinguish
  committed tests from temporary checks; close issues once acceptance criteria
  are met. Keep CI status out of issue comments.
- Use the project opam switch `rocq-cats` with Rocq/Stdlib 9.2 and Dune 3.23.1:
  `opam exec --switch=rocq-cats -- <command>`. Check tool resolution and versions
  before diagnosing failures. Do not change global shell settings or upgrade
  shared environments without explicit authorization.
- Build with the existing VS Code task or `dune build`. Compile affected modules
  and dependents; broaden validation after interface changes. Inspect
  `Print Assumptions` for foundational proofs or suspected hidden axioms.
- Prefer general proofs and temporary checks to redundant tests. Retain tests
  only for concrete interface regressions; keep reusable mathematics in theory
  modules and routine assumption output out of compiled sources.
- Do not edit generated `_build/` files or `rocq-cats.opam` (edit `dune-project`).
  Avoid cleaning without evidence of stale artifacts. Report actual checks,
  toolchain, and remaining limitations; local success does not establish CI.

## Parallel worktrees

- Keep `typeprop` as the integration branch. Start each bounded task from the
  current integrated baseline, on its own short branch and worktree; keep each
  session in its assigned worktree rather than switching another session's branch.
  Only the designated integration session updates `typeprop`; task sessions
  commit and push their own task branches.
- Agree on shared interfaces before parallel implementation. Assign each shared
  foundation to one prerequisite task; integrate it independently, without waiting
  for the rest of that feature. Create dependent task branches only after the
  prerequisite is validated and integrated into `typeprop`; do not implement the
  same foundation twice. If a dependency is discovered on an existing branch,
  pause dependent changes, then rebase onto the updated `typeprop` before resuming.
  Give global renames and reorganizations one owner and integrate them first.
  Before parallel work starts, record the owning session/task, branch and
  prerequisite issue links in the relevant issue so ownership and waiting tasks
  are explicit.
- Keep `_build/` and generated outputs separate per worktree. Reuse the initialized
  toolchain without modifying shared opam environments during parallel work.
  Branches, remotes and stash are shared Git state, not private to each worktree.
- Integrate completed branches one at a time: rebase the task branch onto the
  latest `typeprop`, validate it and its dependents, then fast-forward `typeprop`.
  Record the validated baseline commit. If `typeprop` advances before integration,
  rebase again and revalidate affected modules and dependents before fast-forwarding.
  Do not create merge commits or rewrite `typeprop`. Coordinate rebases of
  published task branches with dependent sessions; use `--force-with-lease`
  when pushing rewritten task history. Avoid repeated cherry-picks of the same
  changes across branches.
- Write bilingual documentation with the code. Run full-library validation and
  export both reading editions after each integrated batch, rather than after
  every intermediate task commit.

## Learnings

- Name concrete Applicative values with an `A` suffix, such as `ReaderA`.
  Keep `Applicative` as the interface class name; underlying functor values
  retain the `F` suffix.
- Name concrete model modules after the model, such as `Instance/Set/Reader.v`.
  Keep shared interface theory in its theory modules, such as `Cat/Applicative/`.
