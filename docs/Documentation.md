# Bilingual reading editions

# 双语阅读版

Presentation conventions are maintained in
[ExportRequirements.md](./ExportRequirements.md). This guide records build
procedures and implementation status. Reading editions come directly from all
modules under [theories/](../theories/), using one compiled bilingual source tree.

展示规范统一维护在 [ExportRequirements.md](./ExportRequirements.md)，本指南记录
构建方法与实现进度。阅读版直接来自 [theories/](../theories/) 下的全部模块，
使用同一份经过编译的双语源码。

HTML and both PDF modes disable coqdoc's built-in symbol substitutions with
native `remove printing` directives in generated inputs. Code retains source
spelling, such as `*`, `->` and `forall`; explicit source printing directives
remain available. The generated preamble shifts `.glob` byte ranges and updates
the source digest, preserving declaration links without editing theory sources.

HTML 与两种 PDF 模式都在生成输入中使用原生 `remove printing` 指令，关闭
coqdoc 内置符号替换。代码保留 `*`、`->`、`forall` 等源码写法，仍允许源码显式
指定打印规则。生成的前言同步平移 `.glob` 字节范围并更新源码校验值，保持声明
链接正确，不修改理论源码。

Section openings use native bilingual coqdoc headings or introductory prose.
They identify the local assumptions and the construction or laws that follow;
both backends preserve these openings before the section's context. See the
[section-opening requirements](./ExportRequirements.md#section-openings).

Section 开场使用原生双语 coqdoc 标题或引言，说明局部假设及接下来的构造或
定律；两种后端均在该段环境声明之前保留开场，遵循
[Section 开场要求](./ExportRequirements.md#section-openings)。

PDF uses the native `\coqdocindent` command to convert coqdoc's half-em source
indentation units to the current code font's actual space width. Constructor
bars follow the [shared source convention](./ExportRequirements.md#constructor-bars),
so source columns agree with native HTML and PDF output.

PDF 通过原生 `\coqdocindent` 命令，将 coqdoc 的半 em 源码缩进单位转换为
当前代码字体的实际空格宽度。构造子竖线遵循
[统一源码约定](./ExportRequirements.md#constructor-bars)，使源码列位置与原生
HTML、PDF 输出一致。

## Full-library export / 全库导出

Run from the repository root in the initialized project environment:

在仓库根目录中，使用已初始化的项目环境运行：

```sh
dune exec tools/docs/docs.exe -- pdf --strict
```

The PDFs are `_build/docs-pdf/en/rocq-cats-en.pdf` and
`_build/docs-pdf/zh/rocq-cats-zh.pdf`. All theory modules are discovered
and ordered automatically. Each export first runs `dune build @all`, and never
edits tracked Rocq sources. Use the project opam switch locally:

PDF 位于 `_build/docs-pdf/en/rocq-cats-en.pdf` 与
`_build/docs-pdf/zh/rocq-cats-zh.pdf`。所有理论模块均自动发现和排序，每次导出先
运行 `dune build @all`，不修改受版本管理的 Rocq 源码。本地使用项目 opam switch：

```sh
opam exec --switch=rocq-cats -- dune exec tools/docs/docs.exe -- pdf --strict
```

PDF uses coqdoc LaTeX followed by two XeLaTeX passes with `-no-shell-escape`.
The complete reading editions and abstract preview share the approved theme in
[pdf-textbook.tex](../tools/docs/pdf-textbook.tex): Pagella prose, JuliaMono
code, Fandol Chinese, quiet blue accents and breakable code frames. It is the
default full-library presentation; further visual-design iteration is paused.
Install JuliaMono Nerd Font with its bold and italic faces; STIX Two Math
supplies fallback symbols.
TeX Live must provide fontspec, geometry, amsmath/amssymb, hyperref, bookmark,
fvextra, newunicodechar, tikz-cd, tcolorbox, titlesec, fancyhdr and TeX Gyre fonts.
The tool does not install dependencies. Locally checked: Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1, TeX Live 2025.

PDF 使用 coqdoc LaTeX 输出，再以 `-no-shell-escape` 运行两次 XeLaTeX。
完整阅读版与抽象范畴预览共用 [pdf-textbook.tex](../tools/docs/pdf-textbook.tex)
中已批准的主题：Pagella 正文、JuliaMono 代码、Fandol 中文、克制的蓝色和可跨页
代码框。这是全库导出的默认样式；后续视觉设计迭代暂时暂停。
需安装 JuliaMono Nerd Font 及其粗体和斜体；备用符号使用 STIX Two Math。
TeX Live 须提供
fontspec、geometry、amsmath/amssymb、hyperref、bookmark、fvextra、newunicodechar、
tikz-cd、tcolorbox、titlesec、fancyhdr 及 TeX Gyre 字体。工具不安装依赖。
本地验证：Rocq/Stdlib 9.2.0、OCaml 5.3.0、Dune 3.23.1、TeX Live 2025。

The exporter and its compiled-source regression use `rocq compile` and
`rocq doc`, available since Rocq 9.0; legacy `coqc`/`coqdoc` executable aliases
are not required.

导出器及其编译源码回归使用 Rocq 9.0 起提供的 `rocq compile` 和 `rocq doc`，
不要求旧的 `coqc`/`coqdoc` 可执行文件别名。

Both PDF modes normalize coqdoc's native blank-row and indentation markers
before layout and shared code-frame decoration, following the
[code-fragment spacing requirements](./ExportRequirements.md#interface-explanations).

两种 PDF 模式都在排版和共用代码框装饰之前，统一处理 coqdoc 的原生空行与
缩进标记，遵循[代码片段间距要求](./ExportRequirements.md#interface-explanations)。

## Complete abstract-category preview / 完整抽象范畴预览

The preview uses the same build, language filtering and reading order:

预览使用相同的构建、语言过滤及阅读顺序：

```sh
dune exec tools/docs/docs.exe -- design --strict
```

Outputs are `_build/docs-design/en/rocq-cats-en.pdf` and
`_build/docs-design/zh/rocq-cats-zh.pdf`. The preview contains every complete
module from `Cats.Cat.Core` through `Cats.Cat.Natural` in shared reading order,
inclusive: currently Core, Terminal, Morphism, Isomorphism, Functor.Core and
Natural. All their coqdoc prose and public declarations are preserved, without
fragment selection or a fixed page count. Earlier prerequisites are still
compiled. Its `reading-order.txt` records only included modules.

输出为 `_build/docs-design/en/rocq-cats-en.pdf` 与
`_build/docs-design/zh/rocq-cats-zh.pdf`。预览包含共享阅读顺序中从
`Cats.Cat.Core` 到 `Cats.Cat.Natural` 两端在内的所有完整模块，目前为 Core、
Terminal、Morphism、Isomorphism、Functor.Core 和 Natural。保留全部 coqdoc
正文与公开声明，不拼接选段或限制页数。此前的基础依赖仍随全库编译；预览的
`reading-order.txt` 只记录实际纳入的模块。

The preview uses the full-library theme and shared code-frame decoration.
Cover and contents reuse the full-library template. Source is never rewritten
for layout. References outside the preview are plain text; included declarations
stay linked. The optional native-proof styling is isolated in
[pdf-proof.tex](../tools/docs/pdf-proof.tex), so the complete PDF needs no
Alectryon installation or proof-style assets.

预览使用全库主题及共用代码框装饰，封面和目录复用全库模板，不为排版改写源码。
预览范围以外的声明引用显示为普通文本，范围内的链接保持可用。可选的原生证明
样式独立保存在 [pdf-proof.tex](../tools/docs/pdf-proof.tex)，因此完整 PDF 不要求
安装 Alectryon 或提供证明样式资源。

Only `design` invokes **Alectryon 2.0.0 with the VsRocq driver**, processing the
original context and proof of `NatIso_is_iso` from
[Natural.v](../theories/Cat/Natural.v). Native LaTeX replaces that declaration's
code block at its original position; other proofs use ordinary coqdoc hiding.
Native focus-bullet annotations show only each branch's current goal, following
[the focused-state requirements](./ExportRequirements.md#focused-proof-states).
There is no diagnostic-command injection, transcript parsing, handwritten goal
or Sphinx build. Generated input, proof, style assets and logs stay in the output
directory and are refreshed each time, without a proof cache.

只有 `design` 调用 **Alectryon 2.0.0 和 VsRocq 驱动**，处理
[Natural.v](../theories/Cat/Natural.v) 中 `NatIso_is_iso` 的原始上下文与证明。
原生 LaTeX 在原位置替换这一声明的代码框，其他证明继续由 coqdoc 常规隐藏。
focus bullet 上的原生注解只显示各分支的当前目标，遵循
[聚焦状态约束](./ExportRequirements.md#focused-proof-states)。不注入诊断命令、
解析终端输出、手写目标或运行 Sphinx。生成的输入、证明、样式及日志保存在输出
目录，每次重新生成，不使用证明缓存。

Install Alectryon on PATH or in this isolated worktree-local environment, which
the exporter finds automatically. The initialized opam environment must supply
compatible `vsrocqtop`. Export never installs dependencies or modifies shared
environments. Ordinary full-library PDF and HTML remain independent of Alectryon.

可将 Alectryon 安装到 PATH，或以下独立 worktree 本地环境，导出器会自动找到。
已初始化的 opam 环境须提供相容的 `vsrocqtop`。导出过程不安装依赖或修改共享
环境；常规全库 PDF 与 HTML 不依赖 Alectryon。

```sh
uv venv --no-python-downloads _build/docs-alectryon
uv pip install --python _build/docs-alectryon/bin/python 'alectryon==2.0.0'
```

## Authoring and order / 写作与排序

Use adjacent, separate coqdoc blocks, English first and Chinese second:

使用相邻且分开的 coqdoc 注释块，先英文后中文：

```coq
(** A universal mediator. *)

(** 泛中介。 *)
```

Library imports from compiled `.glob` metadata determine dependency-first
reading order, shared by PDF and HTML. [docs/chapters](./chapters) gives overall
preferences; local lists such as
[theories/Cat/chapters](../theories/Cat/chapters) refine order. Each optional list
names relative files or directories, one per line. Lists are partial: unlisted
modules stay included; dependencies take precedence. Unknown or repeated entries
fail. A directory may follow an individual file from it without repeating it.
The initial Meta → Set.Core → Set.Morphism → Cat.Core order is automatic.
Each export records its complete order in `reading-order.txt`.

编译 `.glob` 元数据中的导入记录决定依赖优先的阅读顺序，PDF 与 HTML 共用。
[docs/chapters](./chapters) 给整体偏好，
[theories/Cat/chapters](../theories/Cat/chapters) 等局部清单细化顺序。可选清单每行
列一个相对文件或目录，只需列出要调整的部分；未列模块仍纳入，依赖优先于偏好。
未知或重复条目会失败，先列目录内文件再列该目录不会重复文件。开头的
Meta → Set.Core → Set.Morphism → Cat.Core 自动得到；每次导出将完整顺序记录在
`reading-order.txt`。

Reference existing declarations in coqdoc brackets. The lexer handles nested
comments and strings, preserves byte positions and newlines, and updates only
generated `.glob` copies after checking source digests. Printing and visibility
directives remain intact. Ambiguous or unpaired prose goes in `warnings.txt`;
`--strict` rejects it. Use `@lang en`, `@lang zh` or `@lang both` when needed.

通过 coqdoc 括号引用已有声明。词法过滤器识别嵌套注释和字符串，保留字节位置与
换行；检查源码校验值后，只更新生成的 `.glob` 副本。打印与显隐指令保持原样。
歧义或未配对文字记录在 `warnings.txt`，`--strict` 将其视为失败。必要时使用
`@lang en`、`@lang zh` 或 `@lang both`。

The new prose bridges use native LaTeX `\coqref` around coqdoc identifiers for
explicit PDF links, for example
`%\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict}{%[simplex_restrict]%}%`.
Use coqdoc's native destination spelling, where underscores become spaces.
The qualified declaration supplies the destination; the displayed name
remains short. This uses source markup, without changing import handling or
exporter code.

新增承接段落以原生 LaTeX `\coqref` 包裹 coqdoc 标识符，提供显式 PDF 链接，
例如 `%\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict}{%[simplex_restrict]%}%`。
目标使用 coqdoc 的原生拼写，其中下划线变为空格。限定声明提供目标，显示名称
保持简短；这是源码标记，不修改导入处理或
导出器代码。

The simplicial learning strand now follows the abstract category introduction:
ordered shapes → simplicial sets → faces and degeneracies → standard simplices
→ nerves and their vertices, edges and spines → boundaries and horns → filling
and matching → reconstruction and finite products → interval and nerve homotopy.
The preferences in [docs/chapters](./chapters) and
[Simplicial/chapters](../theories/Instance/Set/Simplicial/chapters) keep this strand
ahead of independent STLC, DTT and ETCS directions. General prerequisites still
appear before their clients. The ordinal-nerve comparison follows the interval
chapter because its endpoint compatibility uses that interval interface.

单纯理论学习线现在接在抽象范畴入门之后：有序形状 → 单纯集合 → 面与退化 →
标准单形 → nerve 及其顶点、边与脊 → 边界与 horn → 填充与匹配 → 重构与有限积
→ 区间与 nerve 同伦。[docs/chapters](./chapters) 与
[Simplicial/chapters](../theories/Instance/Set/Simplicial/chapters) 中的偏好使这条
路线先于独立的 STLC、DTT、ETCS 方向展开；通用前置理论仍先于使用者出现。
序数 nerve 的比较放在区间章节之后，因为其端点相容性使用了区间接口。

For a first pass, start with the roadmap in
[Ordinal.v](../theories/Cat/Shape/Ordinal.v), then read the new low-dimensional
explanations in [Core.v](../theories/Instance/Set/Simplicial/Core.v),
[Operators.v](../theories/Instance/Set/Simplicial/Operators.v) and
[Standard.v](../theories/Instance/Set/Simplicial/Standard.v). The prose bridges
refer to the constructions and laws behind each picture. Implementation helpers
and universe transports can be studied on a second pass without losing that
conceptual route. No separate tutorial sources or duplicate proofs are used.

初读可以从 [Ordinal.v](../theories/Cat/Shape/Ordinal.v) 的路线说明开始，再看
[Core.v](../theories/Instance/Set/Simplicial/Core.v)、
[Operators.v](../theories/Instance/Set/Simplicial/Operators.v)、
[Standard.v](../theories/Instance/Set/Simplicial/Standard.v) 新增的低维解释。
承接段落引用每幅图背后的构造与定律；实现辅助项及宇宙运输可在第二遍细读，
不影响先理解概念路线。没有另建教程源码，也没有复制证明。

The cover uses the accepted [logo](./branding/rocq-cats.svg); its
[PNG preview](./branding/rocq-cats-preview.png) is copied without conversion.

封面使用已确认的 [Logo](./branding/rocq-cats.svg)，直接复制其
[PNG 预览](./branding/rocq-cats-preview.png)，无需转换工具。

## Diagrams and checks / 交换图与检查

Shared coqdoc LaTeX islands can contain native TikZ-cd, already loaded by the
preamble. Avoid TeX percent comments inside the island because percent signs
are coqdoc delimiters. HTML omits these PDF-only islands.

共享 coqdoc LaTeX 片段可直接包含 TikZ-cd，模板已加载该包。片段内避免 TeX 百分号
注释，因为百分号是 coqdoc 分隔符。HTML 后端忽略这些 PDF 专用片段。

The simplicial chapters use native TikZ-cd inside coqdoc LaTeX islands for PDF
diagrams, marked `@lang both` for language-neutral labels. English and Chinese
explanation blocks identify the paths and their specified equality.
The diagrams cover shape data, restriction composition and naturality, the
standard-simplex element correspondence, nerve composition and functoriality,
boundary versus horn, horn extension, product projections, ordinal comparison,
homotopy endpoints and the natural-transformation prism. Webpage diagrams are
deferred. These are illustrations of the existing checked interfaces; they add no
mathematical definitions or assumptions. See the
[shared requirements](./ExportRequirements.md#learning-paths-and-mathematical-diagrams).

单纯理论各章在 coqdoc LaTeX 片段中使用原生 TikZ-cd 绘制 PDF 图示，
以 `@lang both` 标记语言中立的标签。英、中解释块说明路径及所用指定相等。
图示覆盖形状数据、限制的复合与自然性、标准单形的元素对应、nerve 的复合与
函子性、边界与 horn 对照、horn 延拓、积投影、序数比较、同伦端点及自然变换
棱柱。网页图示暂缓。这些图解释已有的受检接口，不增加数学定义或假设，遵循
[共享要求](./ExportRequirements.md#learning-paths-and-mathematical-diagrams)。

`--gallina` hides proofs while retaining declarations and data. Missing glyphs,
overfull boxes, invalid references and damaged bookmark strings fail PDF export.
Inspect `xelatex-output.log` for compiler errors and each language's `.log` for
layout diagnostics. All generated files stay under the output directory.
Run `dune runtest tools/docs` for lexical, position, reading-order and real
coqdoc export tests. For visual review, use
`mutool draw -r 120 -o page-%d.png document.pdf`.

`--gallina` 隐藏证明并保留声明和数据。缺字、版面溢出、无效引用及损坏书签会
使 PDF 导出失败。编译错误见 `xelatex-output.log`，排版诊断见各语言的 `.log`。
全部生成文件位于输出目录。`dune runtest tools/docs` 检查词法、位置、阅读顺序
及实际 coqdoc 导出；视觉检查可用
`mutool draw -r 120 -o page-%d.png document.pdf`。

Basic HTML remains available with
`dune exec tools/docs/docs.exe -- build --strict`, opening `_build/docs/index.html`.
It retains coqdoc styling, indices and contents, language/source links and checked
local destinations. Native proof-state integration currently targets the PDF preview.

基础 HTML 通过 `dune exec tools/docs/docs.exe -- build --strict` 导出，入口为
`_build/docs/index.html`。保留 coqdoc 样式、索引、目录、语言和源码链接，并检查
本地目标。原生证明状态集成目前作用于 PDF 预览。
