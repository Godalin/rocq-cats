# Website and book export requirements

# 网页与书籍导出约束

This is the authoritative home for export conventions shared by websites,
HTML reference pages, PDF reading editions and books, in both languages.
Add or revise future presentation requirements here in the same change as
their implementation. Keep commands, dependencies and implementation status
in the [documentation guide](./Documentation.md), linking to these requirements
instead of maintaining competing rules. A requirement does not by itself
claim that every backend already implements it.

本文件是中英文网站、HTML 参考页、PDF 阅读版及书籍导出规范的统一来源。
今后新增或调整此类展示要求，应与实现一起更新本文件。命令、依赖和实现进度
保留在[文档指南](./Documentation.md)，通过链接引用本文件，避免多处维护相互
竞争的规则。规范中的要求不代表所有导出后端都已实现。

## Shared source and native facilities / 共享源码与原生能力

- Generate both languages from the same compiled Rocq sources and bilingual
  coqdoc comments. Preserve mathematical meaning, specified equality, notation,
  source positions and references. Do not duplicate proofs to suit a renderer.
- Prefer native coqdoc, Alectryon and LaTeX facilities with documented extension
  points. Obtain displayed proof states from Rocq through the supported driver;
  do not invent goals, inject diagnostic commands or parse terminal transcripts
  to construct presentation states.
- Keep proof-state extraction optional and targeted. Ordinary reference exports
  must remain independently buildable; export must not modify shared toolchains.

- 两种语言由同一份经过编译的 Rocq 源码和双语 coqdoc 注释生成。保留数学含义、
  指定相等、记号、源码位置和引用；不为适配渲染器而复制证明。
- 优先使用 coqdoc、Alectryon 和 LaTeX 的原生功能及有文档的扩展点。展示状态必须
  通过受支持的驱动从 Rocq 取得；不编造目标，不插入诊断命令或解析终端输出以
  构造展示状态。
- 证明状态提取保持可选且有明确范围。常规参考导出须能独立构建，导出过程不得
  修改共享工具链。

## Focused proof states / 聚焦后的证明状态

When displaying proof states and a tactic creates multiple goals, **display the
current goal after entering each branch's focus, before the tactics that solve it**.
This applies to `split`, `destruct`, `induction`, constructors and other
branching steps.

展示证明状态时，tactic 产生多个目标，**必须在进入每个分支的 focus 后、执行该分支的求解
tactic 前显示当前目标**。这适用于 `split`、`destruct`、`induction`、构造子及
其他产生分支的步骤。

- Keep the unfocused branching step as code only; do not display all pending
  goals immediately after it.
- Enter a real Rocq focus using a bullet or braces, then display only its current
  goal and relevant context. Repeat for each branch and nested branching step.
  Do not include waiting siblings, background goals or completed branches.
- Place the state inside the proof's code frame, directly after the focus
  marker, then continue with the branch's script. Do not collect these states
  into a separate block after the proof.
- Use native sentence annotations to choose these display points. Hiding all
  but the first goal in an unfocused state is not a substitute for real focus.
- Apply the same selection and placement to website and book exports. Native
  folding on a webpage may change visibility, but not which branch a state
  describes or where it belongs in the script.

- 尚未 focus 的分支生成步骤只展示代码，不在其后展开所有待解决目标。
- 使用 bullet 或花括号进入真实 Rocq focus 后，只展示当前目标及相关上下文。
  每个分支及嵌套分支都按此处理，不展示等待中的兄弟目标、后台目标或已完成分支。
- 状态位于证明的同一个代码框内，紧接 focus 标记，之后继续该分支的脚本；不将
  这些状态集中放在证明结束后的独立块中。
- 用原生语句注解选择展示位置。对未 focus 的状态只保留第一个目标，不能代替
  真实 focus。
- 网页与书籍使用相同的状态选择和插入位置。网页可使用原生折叠功能，但不改变
  状态所属的分支或其在脚本中的位置。

For example, annotate the focus bullets, not `split`. Alectryon's input-only
block setting keeps unannotated steps as code; the selected bullets reveal
their focused states using its native output controls.

例如，将注解放在 focus bullet 后，而非 `split` 后。Alectryon 的仅输入块设置
使未注解步骤只显示代码；选中的 bullet 通过原生输出控制展示其聚焦状态。

```coq
Proof.
  apply product_pair_unique. split.
  - (* .unfold .all *)
    exact (limit_β μ false).
  - (* .unfold .all *)
    exact (limit_β μ true).
Qed.
```

See the [native annotation documentation](https://github.com/cpitclaudel/alectryon#controlling-output-in-literate-documents)
and the checked example in [Basics.v](../book/Basics.v).

参见[原生注解文档](https://github.com/cpitclaudel/alectryon#controlling-output-in-literate-documents)
及 [Basics.v](../book/Basics.v) 中经过检查的实例。

## Readability and verification / 可读性与验证

Use restrained textbook styling, distinguish prose from code, preserve readable
Unicode and Chinese text, and handle long declarations and page breaks without
clipping or isolated frame titles. Keep the approved branding and the shared,
dependency-first reading order. Before claiming a presentation change works,
compile the affected sources and dependents, check both languages, render and
inspect changed PDF pages, and check affected HTML output when implemented.
For branching proofs, verify that each selected output follows its focus and
contains only the current goal, with no output at the unfocused branching step.
Report which backends were actually checked and any remaining limitations.

使用克制的教材风格，区分正文与代码，保持 Unicode 和中文清晰可读，处理长声明
及分页时避免裁切或孤立框标题。保留已确认的品牌设计和共享的依赖优先阅读顺序。
宣称展示修改可用前，应编译受影响源码及其依赖者，检查两种语言，渲染并查看有
变化的 PDF 页面，并在已实现相应功能时检查受影响的 HTML 输出。对于分支证明，
确认每份选定状态都紧跟其 focus 且只含当前目标，未 focus 的分支生成步骤后没有
状态输出。报告实际检查的后端及剩余限制。
