# Parallel development with communicating sessions

# 会话通信下的并行开发

[AGENTS.md](../AGENTS.md#parallel-worktrees) states the mandatory rules;
this document explains their execution. Git commits and branch refs record
integration state. Coordinate ongoing work through direct session messages,
without a separate coordination issue or runtime status table.

[AGENTS.md](../AGENTS.md#parallel-worktrees) 规定强制规则，本文说明执行方式。
Git 提交和分支引用记录集成状态，正在进行的工作通过会话直接通信协调，
不另设协调 issue 或运行状态表。

## 1. Roles and starting work / 角色与开始工作

All sessions already exist, and the user designates their roles. No session
creates other sessions or assigns/changes session roles. Only the designated
integrator advances `typeprop`; workers own their task branches and independent
worktrees, including any requested rebases. No session edits another's worktree.

所有会话均已存在，由用户指定角色。会话不创建其他会话，也不指定或更改角色。
只有指定的集成会话推进 `typeprop`；工作会话负责自己的任务分支和独立 worktree，
包括执行所需的 rebase。任何会话都不编辑其他会话的 worktree。

A designated worker starts its task directly. When a stable part is committed
and validated, it sends an integration request. No startup handshake is needed.
Shared foundations and global renames still need one agreed owner and must
integrate before dependent branches start, following the existing rules.

指定的工作会话直接开始任务，完成稳定部分、提交并验证后发送集成请求，
不需要启动握手。共享基础和全局重命名仍按原有规则确定唯一所有者，先集成，
再启动依赖分支。

## 2. Integration request and reply / 集成请求与回复

Use an ordinary message containing three things:

1. **Change:** branch, commit SHA and a short summary.
2. **Validation:** checks run and their results for that commit.
3. **Impact:** affected interfaces/consumers, whether the change is breaking,
   and who may need to synchronize. State uncertainty when impact is unclear.

<!-- Restart numbering for the Chinese translation. -->

1. **修改内容：** 分支、提交 SHA 和简短摘要。
2. **验证情况：** 针对该提交执行的检查及结果。
3. **影响范围：** 受影响的接口／消费者、是否 breaking、谁可能需要同步。
   影响不明确时说明不确定性。

A stable part of a larger task may integrate independently. Keep the requested
branch at the reported SHA while it is being processed. If it needs further
edits, agree with the integrator before replacing the request, then send the
new SHA and validation. No separate proposal, event number or fixed schema
is required.

较大任务中的稳定部分可以先独立集成。处理期间，待集成分支保持在所报 SHA。
需要继续修改时，先与集成会话约定替换请求，再发送新的 SHA 和验证结果。
不需要单独提案、事件编号或固定消息格式。

After checking Git, the integrator replies **“integrated” with the SHA**, or
**“pause” with the reason and next action**. A failed delivery leaves the worker
paused with its work preserved; it must not integrate itself. A pause ends when
the integrator confirms the blocker is resolved.

集成会话核对 Git 后回复“已集成”并附 SHA，或回复“请暂停”并说明原因和下一步。
消息投递失败时，工作会话保全工作并暂停，不自行集成。集成会话确认阻塞解除后
再继续。

## 3. Serial integration / 串行集成

1. Check the requested commit, task scope and prerequisites. Confirm affected
   consumers from the actual declarations/imports and session discussion;
   include implicit parameters, instances, coercions, notation and universes.
2. If the requested commit does not include the latest `typeprop`, ask its
   owner to rebase and revalidate, then report the new SHA. Coordinate published
   rewrites and use
   `--force-with-lease`. Never rebase another session's checkout.
3. Validate the exact candidate and affected dependents with the project
   `rocq-cats` switch. Apply the existing mathematical and bilingual documentation
   requirements, checking `Print Assumptions` when appropriate. Keep build
   outputs separate per worktree; do not modify shared toolchains.
4. For breaking changes, first ask affected workers to preserve work and pause;
   wait for their explicit confirmation. Before advancing, confirm the candidate
   and `typeprop` still match the validated SHAs and the integration checkout is
   clean. Fast-forward one branch at a time with `git merge --ff-only <sha>`;
   allow no merge commits or rewriting of `typeprop`. Changed SHAs require
   renewed validation.
5. Verify the resulting Git ref, reply to the origin and notify affected workers.
   Failure before advancement leaves `typeprop` unchanged. If notification or
   push fails after advancement, inspect refs before retrying; do not integrate
   the same change twice or claim remote publication without verifying it.

<!-- Restart numbering for the Chinese translation. -->

1. 核对请求提交、任务范围和前置依赖。结合实际声明／导入和会话讨论确认消费者，
   包括隐式参数、实例、强制转换、记号和宇宙约束的影响。
2. 请求提交未包含最新 `typeprop` 时，请所有者 rebase 并重新验证，报告新 SHA。
   改写已发布历史须协调并使用 `--force-with-lease`；不 rebase 其他会话的
   checkout。
3. 使用项目 `rocq-cats` switch 验证精确候选及受影响依赖方，遵守原有数学和
   双语文档要求，按需检查 `Print Assumptions`。各 worktree 的构建输出独立，
   不修改共享工具链。
4. breaking 变更先请受影响工作会话保全并暂停，等待明确确认。推进前确认候选与
   `typeprop` 仍对应已验证 SHA，且集成 checkout 干净。逐分支使用
   `git merge --ff-only <sha>` 快进，不产生 merge commit 或改写 `typeprop`。
   SHA 改变时须重新验证。
5. 核实结果 ref，回复来源会话并通知受影响会话。推进前失败须保持 `typeprop`
   不变；推进后通知或推送失败时，先检查 refs 再重试，不重复集成，也不在核实
   前声称远端已发布。

Integration acceptance requires the library to build successfully with the
project toolchain: `opam exec --switch=rocq-cats -- dune build @all`. A library
build failure blocks acceptance until repaired. HTML/PDF exports are separate
documentation tasks, performed when requested according to
[the documentation guide](./Documentation.md); they are not routine integration
or batch acceptance requirements. Preserve integrated history and distinguish
local validation from CI.

集成验收以项目工具链下库构建通过为准：
`opam exec --switch=rocq-cats -- dune build @all`。库构建失败时须先修复，
再完成验收。HTML／PDF 导出作为独立文档任务，在有要求时按
[文档指南](./Documentation.md)执行，不作为常规集成或批次验收要求。
保留已集成历史，区分本地验证和 CI。

## 4. Notifications and synchronization / 通知与同步

Route by semantic impact on active work. The worker reports likely impact;
the integrator confirms it. If uncertain, ask the relevant sessions or widen
notification scope. A changed file count or directory alone cannot determine it.

按对活跃工作的语义影响选择接收者，由工作会话说明预期影响，集成会话确认。
不明确时询问相关会话或扩大通知范围，不能仅凭修改文件数量或所在目录判断。

| Scope / 范围 | Recipients / 接收者 | Typical effect / 典型影响 |
| --- | --- | --- |
| L0 Local / 局部 | Origin worker / 来源会话 | Private proof/implementation, unchanged public behavior / 私有证明或实现，公共行为不变 |
| L1 Targeted / 定向 | Origin and affected consumers / 来源及受影响消费者 | Shared API or dependency used by particular tasks / 特定任务使用的共享 API 或依赖 |
| L2 Global / 全局 | All active workers / 全部活跃工作会话 | Foundational contracts, global notation/instances, toolchain or workflow / 基础契约、全局记号／实例、工具链或流程 |

A notification gives the integrated SHA, relevant change and required action.
Breaking is independent of scope. After a breaking integration, affected workers
synchronize, validate their dependents and confirm completion before resuming
related edits. Only request confirmation when a pause or synchronization needs
it; message delivery or silence is not confirmation that the action is complete.

通知说明集成 SHA、相关变化和所需动作。breaking 与通知范围独立。breaking
集成后，受影响工作会话同步、验证依赖方并确认完成，再恢复相关编辑。只在暂停
或同步确实需要时要求确认；投递成功或沉默不代表动作已完成。

Synchronize at a safe checkpoint after preserving local/user work. A nonbreaking
notice does not require an immediate rebase: synchronize before using the new
contract or starting new dependent work. Coalesce related notices and avoid
routine commit/build broadcasts. Preserve explicit pause/sync instructions.

先保全本地／用户工作，再在安全点同步。非 breaking 通知不要求立即 rebase，
在使用新契约或开始新的依赖工作前完成同步即可。合并相关通知，不广播例行提交
或构建状态；明确的暂停／同步要求不能省略。

## 5. Problems and recovery / 问题与恢复

| Situation / 情形 | Action / 动作 |
| --- | --- |
| Dirty worktree or running build / 脏工作区或正在构建 | Reach a safe checkpoint and preserve work before Git operations; never discard user edits / 到安全点并保全后再操作 Git，不丢弃用户编辑 |
| Conflict or failed validation / 冲突或验证失败 | Tell the owner which commit/check failed; repair and revalidate before integration / 告知所有者失败提交／检查，修复并重验后再集成 |
| Missing, repeated or late message / 漏收、重复或迟到消息 | Check Git ancestry and ask the sender what remains pending; never repeat an already completed integration / 检查 Git 祖先关系并向发送者确认待办，不重复已完成集成 |
| Unreachable session / 会话失联 | Preserve work and pause the affected task/handoff until contact resumes / 保全并暂停受影响任务／交接，恢复联系后再继续 |
| Restart or uncertain push result / 重启或推送结果不明 | Inspect actual local/remote refs, then confirm unfinished actions through normal messages / 检查真实本地／远端 refs，通过正常消息核对未完成动作 |
| Coordinator replacement or overlapping ownership / 协调者更换或归属重叠 | Pause disputed work; the user designates any replacement session, and the old coordinator must release authority or stop before the new one integrates / 暂停争议工作；替代会话由用户指定，旧协调者交接或停止后新会话才可集成 |

For experimental preservation, follow the existing named-stash requirements;
never automatically stash, reapply, discard or clean work. Recovery uses Git and
direct messages, without a startup handshake or an additional state database.

实验保存遵循原有的命名 stash 要求，不自动 stash、恢复、丢弃或 clean 工作。
恢复依靠 Git 和会话直接通信，不增加启动握手或另一套状态数据库。

## 6. Checking the workflow / 验证流程

Evaluate ordinary integration, a requested pause, each notification scope,
breaking synchronization, and stale/failed requests. Use Git history, actual
build results and session messages to check outcomes, including missed/repeated
messages and recovery. This document prescribes the workflow, not current tasks
or trial results. Keep lasting task conclusions in the relevant issue under
the existing rules; do not include CI status in issue comments. Defer reusable
skill extraction until the concrete workflow has been tested.

验证正常集成、要求暂停、各通知范围、breaking 同步，以及过时／失败请求。
用 Git 历史、实际构建结果和会话消息核实结果，包括漏收／重复消息及恢复。
本文只规定流程，不记当前任务或试验结果。长期任务结论按原有规则更新到相关
issue，留言不记 CI 状态；具体流程实测后再考虑提取通用技能。
