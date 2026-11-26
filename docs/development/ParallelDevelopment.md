# Parallel development with communicating sessions

[AGENTS.md](../../AGENTS.md#parallel-worktrees) states the mandatory rules;
this document explains their execution. Git commits and branch refs record
integration state. Coordinate ongoing work through direct session messages,
without a separate coordination issue or runtime status table.

## 1. Roles and starting work

All sessions already exist, and the user designates their roles. No session
creates other sessions or assigns/changes session roles. Only the designated
integrator advances `typeprop`; workers own their source branches and independent
worktrees. The integrator rebases submitted commits in its own temporary branch
and reusable validation worktree. No session edits another's worktree.

A designated worker starts its task directly. When a stable part is committed
and validated, it sends an integration request. No startup handshake is needed.
Shared foundations and global renames still need one agreed owner and must
integrate before dependent branches start, following the existing rules.

During editing, build concrete affected targets and representative consumers.
For broad foundational/API refactors, settle design and naming before running
the necessary full validation for the stable submission; do not rerun
`@all @runtest @install` after each small edit. Reuse passed checks when their
source/dependencies, toolchain and check inputs are unchanged; rerun for relevant
changes, failures or unresolved concerns. Build dependencies before temporary
audits. Select assumption, strict-universe and computation checks by impact,
without mechanically repeating every historical audit. The integrator still
validates the exact resulting SHA under the acceptance rule below.

## 2. Integration request and reply

Use an ordinary message containing three things:

1. **Change:** branch, commit SHA and a short summary.
2. **Validation:** checks run and their results for that commit.
3. **Impact:** affected interfaces/consumers, whether the change is breaking,
   and who may need to synchronize. State uncertainty when impact is unclear.

<!-- Restart numbering for the Chinese translation. -->

A stable part of a larger task may integrate independently. Its submitted SHA
need not contain the latest `typeprop`; the integrator handles that rebase.
Keep the source branch at the reported SHA while it is being processed. If it
needs further edits, agree with the integrator before replacing the request,
then send the new SHA and validation. No separate proposal, event number or
fixed schema is required.

After checking Git, the integrator replies **“integrated” with the resulting
SHA** (and source SHA if rebased), or **“pause” with the reason and next action**.
A failed delivery leaves the worker paused with its work preserved; it must not
integrate itself. A pause ends when the integrator confirms the blocker is
resolved.

After integration, start the next bounded task on a new short branch from the
reported integrated baseline. Keep any remaining unintegrated work and adapt
only that remainder; do not replay patches already accepted under new SHAs.

Periodically, each owner may remove obsolete local and remote task branches
once the integrator has confirmed all their changes are accepted, source/result
SHAs are recorded, and no pending request, dependent task or unintegrated work
remains. Retain branches still needed for audit or recovery, or whose status is
uncertain. For rebased integration, verify the source/result mapping and patch
equivalence; `git branch --merged` alone is insufficient. If the exact original
commits must remain available, retain a durable Git ref: recording their SHAs
alone does not keep them reachable. Check worktree attachments before deleting
branches, switching only your own clean worktree when needed. Branch cleanup
does not require removing worktrees or clearing their reusable build caches.

## 3. Serial integration

1. Check the requested commit, task scope and prerequisites. Confirm affected
   consumers from the actual declarations/imports and session discussion;
   include implicit parameters, instances, coercions, notation and universes.
2. Create an integrator-owned temporary branch from the submitted SHA in a
   reusable validation worktree. Rebase onto the latest `typeprop` when needed,
   leaving the worker's branch/worktree unchanged. Resolve unambiguous mechanical
   conflicts; return conflicts requiring proof, API or design changes to the
   worker. Compare the original and rebased changes before accepting the result.
3. Validate the exact resulting candidate and affected dependents with the project
   `rocq-cats` switch. Apply the existing mathematical and source coqdoc
   requirements, checking `Print Assumptions` when appropriate. Keep build
   outputs separate per worktree; do not modify shared toolchains.
4. For breaking changes, first ask affected workers to preserve work and pause;
   wait for their explicit confirmation. Before advancing, confirm the candidate
   and `typeprop` still match the validated SHAs and the integration checkout is
   clean. Fast-forward one branch at a time with `git merge --ff-only <sha>`;
   allow no merge commits or rewriting of `typeprop`. If the baseline advances,
   the integrator rebases again in its worktree and renews validation. Any other
   candidate SHA change also requires renewed validation.
5. Verify the resulting Git ref, reply to the origin and notify affected workers.
   Failure before advancement leaves `typeprop` unchanged. If notification or
   push fails after advancement, inspect refs before retrying; do not integrate
   the same change twice or claim remote publication without verifying it.

<!-- Restart numbering for the Chinese translation. -->

Integration acceptance requires the library to build successfully with the
project toolchain: `opam exec --switch=rocq-cats -- dune build @check-library`,
plus relevant regressions selected by [the testing guide](Testing.md).
Task checkpoints use affected targets; complete tests remain in CI. A library
build failure blocks acceptance until repaired. HTML/PDF exports are separate
documentation tasks, performed when requested according to
[the documentation guide](Documentation.md); they are not routine integration
or batch acceptance requirements. Preserve integrated history and distinguish
local validation from CI.

## 4. Notifications and synchronization

Route by semantic impact on active work. The worker reports likely impact;
the integrator confirms it. If uncertain, ask the relevant sessions or widen
notification scope. A changed file count or directory alone cannot determine it.

| Scope | Recipients | Typical effect |
| --- | --- | --- |
| L0 Local | Origin worker | Private proof/implementation, unchanged public behavior |
| L1 Targeted | Origin and affected consumers | Shared API or dependency used by particular tasks |
| L2 Global | All active workers | Foundational contracts, global notation/instances, toolchain or workflow |

A notification gives the integrated SHA, relevant change and required action.
Ordinary notices need no acknowledgment. Breaking is independent of scope:
affected workers preserve and pause before integration, then synchronize,
validate and confirm before resuming related edits. A nonbreaking notice allows
synchronization at a safe checkpoint before using the new contract.

Request confirmation only for required pause/sync actions. Before changing a
shared toolchain, every affected session explicitly confirms it has stopped
using it; delivery or silence is insufficient. A confirmation needs only the
completed action, such as “Stopped using the shared switch”; add details only
for blockers or uncertainty. Preserve work locally without repeating branch/ref
inventories. Do not reply merely to acknowledge a confirmation; integration
result replies remain required.

Combine related updates in your own pending message when supported. Skip routine
progress/build/standby notices and statuses superseded by confirmed results.
Do not repeat validation or reread confirmed sessions for the same action;
consult context or Git only for unresolved or conflicting facts.

## 5. Problems and recovery

| Situation | Action |
| --- | --- |
| Dirty worktree or running build | Reach a safe checkpoint and preserve work before Git operations; never discard user edits |
| Conflict or failed validation | Integrator handles mechanical rebases; report substantive conflicts or failures to the worker, then validate the repaired result |
| Missing, repeated or late message | Check Git history and source/result SHAs in replies; rebased source SHAs may not be ancestors, so confirm equivalent patches before replaying |
| Unreachable session | Preserve work and pause the affected task/handoff until contact resumes |
| Restart or uncertain push result | Inspect actual local/remote refs, then confirm unfinished actions through normal messages |
| Coordinator replacement or overlapping ownership | Pause disputed work; the user designates any replacement session, and the old coordinator must release authority or stop before the new one integrates |

For experimental preservation, follow the existing named-stash requirements;
never automatically stash, reapply, discard or clean work. Recovery uses Git and
direct messages, without a startup handshake or an additional state database.

## 6. Checking the workflow

Evaluate ordinary integration, a requested pause, each notification scope,
breaking synchronization, and stale/failed requests. Use Git history, actual
build results and session messages to check outcomes, including missed/repeated
messages and recovery. This document prescribes the workflow, not current tasks
or trial results. Keep lasting task conclusions in the relevant issue under
the existing rules; do not include CI status in issue comments. Defer reusable
skill extraction until the concrete workflow has been tested.
