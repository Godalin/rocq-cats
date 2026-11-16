# Development checks and testing / 开发检查与测试

Use the existing `rocq-cats` opam switch: Rocq 9.3.0, Stdlib 9.2.0 and
Dune 3.23.1. Validation grows with the change's semantic impact, rather than
running the entire repository after every edit. All commands below perform
ordinary proof checking; none enables `vos` or skips obligations.

使用现有 `rocq-cats` opam switch：Rocq 9.3.0、Stdlib 9.2.0 和 Dune 3.23.1。
验证范围随修改的语义影响扩大，不在每次编辑后重跑整个仓库。下列入口均执行
正常的证明检查，不启用 `vos`，也不跳过义务。

## Check selection / 选择检查范围

| Stage | Required checks |
| --- | --- |
| Editing | Changed modules, then representative consumers and regressions relevant to the change. |
| Stable task checkpoint | Affected theory and test targets; record coverage and remaining uncertainty. A local commit alone does not require a full library or test build. |
| Broad foundation/API change | Freeze the interface, names and formatting; build the library and relevant regressions once. Use all tests when many test families are affected or the consumer boundary is uncertain. |
| Integration | Build the complete library and relevant regressions at the exact resulting candidate SHA. Renew affected checks after a rebase; reuse unchanged artifacts through Dune. |
| CI | Keep the existing complete repository, test and install checks. Documentation export remains separate from ordinary local acceptance. |

| 阶段 | 必需检查 |
| --- | --- |
| 编辑中 | 修改模块，再选择有代表性的消费者及与本次修改相关的回归。 |
| 稳定任务检查点 | 受影响的理论及测试目标，记录覆盖范围和未解疑问；本地提交本身不要求全库或全部测试。 |
| 广泛基础／API 修改 | 收齐接口、命名及排版后，统一构建库及相关回归；影响多个测试词族或消费者边界不明确时，再做一次全部测试。 |
| 集成 | 对最终候选的精确 SHA 构建完整库及相关回归；重基后更新受影响检查，通过 Dune 复用未变产物。 |
| CI | 保留现有全仓库、测试及安装检查；文档导出仍不属于普通本地验收。 |

Formatting-only Rocq edits normally need only their module targets during
editing. Proof-only edits also need consumers when transparency, conversion
or computation may change. A typeclass/coercion/notation/universe change
needs representative clients exercising that behavior, even if the defining
module itself compiles. Do not label selected checks as full validation.

纯排版 Rocq 修改在编辑期间通常只需编译对应模块。只改证明时，若可能影响透明性、
定义相等或计算，还需检查消费者。类型类、强制转换、记号及宇宙修改，即使定义模块
自身可编译，也要选择实际使用该行为的客户端；不得把定向检查称为全量验证。

## Commands and coverage / 命令及覆盖范围

```sh
# One module and an explicitly selected consumer / 单模块及明确选择的消费者
opam exec --switch=rocq-cats -- dune build \
  theories/Cat/Core.vo theories/Cat/Functor/Core.vo

# Foundational regressions / 基础回归
opam exec --switch=rocq-cats -- dune build @check-core

# Complete library, without test modules or exports / 完整库，不含测试模块及导出
opam exec --switch=rocq-cats -- dune build @check-library

# All Rocq regression modules and their test aliases / 全部 Rocq 回归模块及其测试别名
opam exec --switch=rocq-cats -- dune build @check-tests

# One regression family / 一个回归词族
opam exec --switch=rocq-cats -- dune build @tests/horn-attachment/runtest
```

`@check-core` contains `CoreInterfaces`, `AlgebraNotation`,
`MonoidExtensions`, `GroupExtensions` and `BundledGroupoid`. It checks
selected category/algebra interfaces and their actual clients; it is not a
universal substitute for selecting tests. Add the relevant module or test
family for products, monads, Topos, DTT, STLC or simplicial constructions.
The category-only regression can also be built as
`tests/CoreInterfaces.vo`; it does not import the broad `Interfaces` suite.

`@check-core` 包含 `CoreInterfaces`、`AlgebraNotation`、
`MonoidExtensions`、`GroupExtensions` 和 `BundledGroupoid`，
覆盖选定范畴／代数接口及其实际客户端，不是通用的测试选择替代品。
修改积、Monad、Topos、DTT、STLC 或单纯集构造时，另选相关模块或测试词族。
基础范畴回归也可单独构建 `tests/CoreInterfaces.vo`，不导入广泛的
`Interfaces` 测试集合。

`@check-library` recursively selects `theories/all`; it includes every
library module without a maintained filename list. `@check-tests` selects
both `tests/all` and `tests/runtest` recursively, so it includes root-level
regressions omitted from the older root `runtest` list as well as nested test
theories. It builds any library dependencies needed by those tests; it does
not independently require the entire library. Tooling tests under
`tools/docs` remain covered by the existing `@runtest` CI command.
Neither alias invokes HTML/PDF exports or installation.

`@check-library` 递归选择 `theories/all`，无须维护文件名清单即可覆盖全部库模块。
`@check-tests` 递归选择 `tests/all` 及 `tests/runtest`，同时覆盖旧根目录
`runtest` 清单未列出的根级回归，以及子目录测试理论；它会构建测试实际需要的
库依赖，但不额外要求整个库。`tools/docs` 下的工具测试仍由现有 CI 的
`@runtest` 命令覆盖。两个别名均不导出 HTML／PDF，也不执行安装。

The existing `dune build @all @runtest @install` remains a complete
repository/package check, not the default edit loop. Library proofs themselves
are checked when their `.vo` files are built; skipping regression modules
during editing does not skip those proofs. Regression modules additionally
exercise public inference, import boundaries, universes and concrete reduction.

现有 `dune build @all @runtest @install` 仍是完整仓库／打包检查，不作为默认
编辑循环。构建库的 `.vo` 时已检查其中的证明，编辑期间不跑回归模块不会跳过
库内证明；回归另行覆盖公开推断、导入边界、宇宙及具体归约等行为。

## Reuse and reporting / 复用与报告

Keep each worktree's `_build` directory and reuse the initialized toolchain.
Do not clean without evidence of stale artifacts, copy generated files between
worktrees or change shared toolchains to accelerate a local check. Let Dune
track actual dependencies; directory names or a text search alone do not prove
that an API change has no consumers. A changed library module target builds
its prerequisites, not all of its reverse dependents.

保留每个 worktree 的 `_build`，复用已初始化工具链。无陈旧产物证据时不清理，
不在 worktree 间复制生成文件，也不为加速本地检查而更改共享工具链。实际依赖
由 Dune 跟踪；仅凭目录或文本搜索不能证明 API 修改没有消费者。构建一个修改后的
库模块会补齐它的前置依赖，不会自动检查全部反向依赖。

Freeze broad changes before starting expensive validation. Do not add routine
formatting while that validation runs. Repeat checks for changed relevant
inputs, failures or unresolved concerns; do not repeat an unchanged full pass
at every task boundary. Integration still validates its exact candidate SHA.
Report selected targets, toolchain, results and omitted coverage. HTML/PDF
exports and install checks run when their own task or CI requires them.

在昂贵验证前收齐广泛修改，不在验证过程中追加例行排版。仅因相关输入变化、失败或
未解疑问而重跑检查，不在每个任务边界重放未变化的完整检查；集成仍验证精确候选
SHA。报告实际目标、工具链、结果及未覆盖范围；HTML／PDF 导出与安装检查仅在
对应任务或 CI 要求时运行。

Large libraries use the same separation: MathComp groups related files into
independently compilable packages, while mathlib provides CI-built artifacts
for developers to download. Rocq also supports `vos` development interfaces,
but those skip opaque proofs and require later full checking; transparent
computational witnesses in this project must remain available.

大型库采用类似分工：MathComp 将相关文件组成独立编译包，mathlib 提供由 CI
生成的编译缓存供开发者下载。Rocq 也支持 `vos` 开发接口，但它跳过不透明证明，
后续仍需完整检查；本项目的透明计算见证仍须保持可用。

References / 参考：
[MathComp build layout](https://github.com/math-comp/math-comp/blob/master/INSTALL.md),
[mathlib build cache](https://github.com/leanprover-community/mathlib4#downloading-cached-build-files),
[Rocq compiled interfaces](https://rocq-prover.org/doc/V9.3.0/refman/practical-tools/coq-commands.html#compiled-interfaces-produced-using-vos).
