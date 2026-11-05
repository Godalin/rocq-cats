# Bilingual reference and checked tutorials

# 双语参考手册与经过检查的教程

The documentation uses the same Rocq sources for both languages. Library
reference pages come from `theories/`; narrative chapters live in `book/`.
Both use adjacent English-first, Chinese-second coqdoc blocks. Definitions,
examples and proofs are shared and compiled once by Dune.

两种语言使用同一套 Rocq 源码。库的参考页面来自 `theories/`，叙述式章节位于
`book/`。二者均使用相邻、分开的 coqdoc 注释块，先英文后中文。定义、示例与
证明共享，由 Dune 编译一次。

## Build / 构建

With the initialized project toolchain, run:

在已初始化的项目工具环境中运行：

```sh
dune exec tools/docs/docs.exe -- build --strict
```

For the local Nix/opam setup, use:

本地 Nix/opam 环境使用：

```sh
opam exec --switch=rocq-env -- nix-shell --run \
  'dune exec tools/docs/docs.exe -- build --strict'
```

Open `_build/docs/index.html`, then choose English or Chinese. The corresponding
entry points are `_build/docs/en/index.html` and `_build/docs/zh/index.html`.
Every page has language switching, an index and a link to the original bilingual
source. Cross-module references and Unicode symbol anchors are checked locally.

打开 `_build/docs/index.html`，选择英文或中文。两种语言的入口分别为
`_build/docs/en/index.html` 和 `_build/docs/zh/index.html`。页面提供语言切换、
索引和原始双语源码链接。构建检查跨模块引用及 Unicode 符号锚点。

For the limit chapter and its transitive reference dependencies only, run:

只生成极限章节及其引用的传递依赖时运行：

```sh
dune exec tools/docs/docs.exe -- build --sample --strict
```

This writes `_build/docs-sample/`, independently of the complete site. The
generator first runs `dune build @all`, so references and tutorial examples
always use current compiled modules. Generation never edits tracked `.v` files.

这会独立写入 `_build/docs-sample/`。生成器先运行 `dune build @all`，确保引用与
教程示例使用当前编译结果。生成过程不会修改受版本管理的 `.v` 文件。

## Language convention / 语言约定

```coq
(** A universal mediator. *)

(** 泛中介。 *)

Definition ...
```

The filter recognizes Rocq strings and nested comments. It masks unwanted
documentation with spaces while keeping every byte position and newline.
Code, ordinary comments, printing directives and visibility directives remain
unchanged. Language detection ignores coqdoc code brackets, verbatim blocks,
math and raw-output islands. In an adjacent translation pair, the second block
may contain English technical names such as `Hom` or `Type`.

过滤器识别 Rocq 字符串及嵌套注释。它用空格遮蔽另一语种的文档，保留每个字节
位置和换行。代码、普通注释、打印指令与显隐指令保持原样。语言检测忽略 coqdoc
代码括号、逐字块、数学及原始输出区域。相邻翻译对的第二块可以包含 `Hom`、
`Type` 等英文技术名称。

Unpaired language blocks produce diagnostics. An unclassified mixed-language
block is retained in both outputs and reported in `warnings.txt`; `--strict`
rejects these diagnostics. A deliberately single-language or shared block can
use an explicit first-line marker, removed from the generated documentation:

未配对的语言块会产生诊断。无法分类的混合语言块保留在两种输出中，并记录到
`warnings.txt`；`--strict` 将这些诊断视为失败。刻意使用单语或共享内容的块可以
在首行添加显式标记；标记不会出现在生成文档中：

```coq
(** @lang en
    An English-only explanation. *)

(** @lang zh
    仅中文的说明。 *)

(** @lang both
    [∀ x, x ≈ x] *)
```

Use markers only where the existing translation convention cannot express the
intent. Shared notation and snippets normally need no marker.

只在现有翻译约定无法表达意图时使用标记。共享记号和代码片段通常不需要标记。

## References and presentation / 引用与展示

Original `.glob` positions remain valid because filtering preserves byte
offsets. The generated copy receives an updated digest after the original
digest is checked. Missing or stale metadata causes an error. Source metadata
is never changed.

过滤保留字节偏移，因此原 `.glob` 的位置仍有效。检查原校验值后，为生成副本
写入更新后的校验值。缺失或过期的元数据会导致报错。原元数据不作修改。

Rocq 9.0 can emit unresolved local aliases for record fields, recursive
definitions and match binders. Generated metadata redirects aliases to known
declarations; variables without a known declaration are displayed as text.
Named record constructors missing an HTML anchor receive one at their visible
declaration, identified by metadata. Public destinations are then checked.

Rocq 9.0 有时为记录字段、递归定义及匹配绑定变量输出无法解析的局部别名。
生成元数据将别名重定向到已知声明；无已知声明的变量显示为文本。具名记录
构造器若缺少 HTML 锚点，则依据元数据在实际显示位置补齐。之后检查公开跳转目标。

The exporter uses `--gallina`, which hides proofs while retaining statements,
data definitions, notations and arguments. It does not use `--light`.
Coqdoc syntax such as `(* begin hide *)` / `(* end hide *)` remains available.
HTML is static and can be read offline, including all generated local links.

导出器使用 `--gallina` 隐藏证明，同时保留陈述、数据定义、记号和参数声明；
不启用 `--light`。仍可使用 `(* begin hide *)` / `(* end hide *)` 等 coqdoc
语法。HTML 为静态页面，生成的本地链接可以离线阅读。

## Writing alongside development / 与开发同步写作

[The limit chapter](../book/Limits.v) is the first example: cones, their universal
mediators, terminal cones and the diagonal adjunction. It imports existing
theory modules, explains their relationship, and includes three checked worked
examples. Proofs are hidden in the reading view and available through Source.

[极限章节](../book/Limits.v) 是首个示例：锥、泛中介、终锥及对角伴随。它导入已有
理论模块，解释它们之间的联系，并提供三个经过检查的例题。阅读视图隐藏证明，
可通过源码链接查看。

When adding a construction, update the corresponding narrative section and its
translation, referencing library identifiers in coqdoc brackets. Put executable
examples directly in the chapter. Dune discovers new chapters in `book/`, and
the complete export includes them automatically. Source order is shared by both
languages; mathematical chapter order need not follow library dependency order.

新增构造时，同步更新相应叙述章节及其翻译，通过 coqdoc 括号引用库标识符。
将可执行示例直接写入章节。Dune 会发现 `book/` 中的新章节，完整导出自动包含
这些章节。两种语言共享源码顺序；数学章节顺序不必沿库的依赖顺序排列。

## PDF export / PDF 导出

PDF is a separate, optional target. To export just the checked tutorial in
both languages:

PDF 是独立的可选目标。只导出经过检查的双语教程：

```sh
dune exec tools/docs/docs.exe -- pdf --book --strict
```

The outputs are `_build/docs-pdf/book/en/rocq-cats-en.pdf` and
`_build/docs-pdf/book/zh/rocq-cats-zh.pdf`. Use `pdf --sample --strict` for
the limits chapter plus its API dependencies, or `pdf --strict` for the full
reference and tutorials. These write separate `sample/` and `full/` directories
under `_build/docs-pdf/`, with the same language/file layout. The full reference
is several hundred pages; `--book` is the smaller reading edition.

输出为 `_build/docs-pdf/book/en/rocq-cats-en.pdf` 和
`_build/docs-pdf/book/zh/rocq-cats-zh.pdf`。使用 `pdf --sample --strict` 导出
极限章节及其 API 依赖，或使用 `pdf --strict` 导出全库参考手册和教程。它们分别
写入 `_build/docs-pdf/` 下独立的 `sample/` 和 `full/` 目录，语言及文件布局相同。
全库参考手册有数百页；`--book` 是较短的教程阅读版。

The same Nix/opam wrapper applies, for example:

同样可以通过本地 Nix/opam 环境运行：

```sh
opam exec --switch=rocq-env -- nix-shell --run \
  'dune exec tools/docs/docs.exe -- pdf --book --strict'
```

PDF additionally requires XeLaTeX and TeX Live packages for CTeX/Fandol,
DejaVu, STIX Two Math, fontspec, geometry, hyperref, bookmark, fvextra,
newunicodechar. The tested setup is TeX Live 2025, XeTeX
0.999997. Fonts are selected by TeX font filenames, avoiding OS-specific
font names. These tools were already supplied by the local Nix profile;
ordinary HTML export and tests do not require TeX. No automatic dependency
installation occurs.

PDF 另外需要 XeLaTeX 及 TeX Live 中的 CTeX/Fandol、DejaVu、STIX Two Math、
fontspec、geometry、hyperref、bookmark、fvextra 和 newunicodechar。
已验证的版本为 TeX Live 2025、XeTeX 0.999997。通过 TeX 字体文件名选择字体，
避免依赖操作系统专用字体名称。本地工具来自已有 Nix 配置；普通 HTML 导出和
测试无需 TeX。工具不会自动安装依赖。

The exporter runs coqdoc's LaTeX backend on the same filtered sources and
metadata, then XeLaTeX twice for contents and references. It retains
declarations and hides proofs, just like HTML. Generated TeX, filtered inputs,
source copies, the coqdoc stylesheet and logs remain beside the PDFs.
Inspect `xelatex-output.log` for a compiler failure and `rocq-cats-en.log` or
`rocq-cats-zh.log` for detailed layout diagnostics. An input digest invalidates
only the generated `.aux`, `.toc` and `.out` files when content or presentation
changes, so old contents macros cannot leak into the next build.

导出器对相同的过滤源码和元数据运行 coqdoc 的 LaTeX 后端，再运行两次 XeLaTeX
生成目录和引用。与 HTML 一样，它保留声明并隐藏证明。生成的 TeX、过滤输入、
源码副本、coqdoc 样式和日志均保存在 PDF 附近。编译失败时查看
`xelatex-output.log`；详细排版诊断位于 `rocq-cats-en.log` 或
`rocq-cats-zh.log`。输入校验值在内容或排版变化时，仅使生成的 `.aux`、`.toc` 和
`.out` 文件失效，避免旧目录中的宏残留到下一次构建。

Presentation adjustments are confined to generated LaTeX: repeated code
blank lines are compacted, tutorial headings are promoted, long module names
can wrap, and Unicode symbols fall back to STIX when the current font lacks
a glyph. Missing glyphs, overflowing boxes, undefined references, duplicate
labels and broken bookmark strings fail the export. The regular test suite
covers these presentation checks without requiring a TeX installation.
This is a coqdoc reading edition, not a semantic translation of arbitrary
Rocq formulas into conventional mathematical notation.

排版调整仅作用于生成的 LaTeX：合并代码中的连续空行、提升教程标题层级、允许
长模块名换行，并在当前字体缺字时为 Unicode 符号使用 STIX 回退。缺字、版面
溢出、未定义引用、重复标签和损坏的书签字符串都会使导出失败。普通测试覆盖
这些排版检查，无需安装 TeX。这是 coqdoc 阅读版，不会将任意 Rocq 公式进行
语义转换后重写为传统数学记号。

## Validation and scope / 验证与范围

Locally validated with Rocq/coqdoc 9.0.1, OCaml 5.3.0 and Dune 3.23.1. The tool
uses only OCaml standard libraries (`Unix`, `Str`; OCaml 4.14 or newer) and the
existing Rocq toolchain. The project workflow also runs the strict sample export
in its existing Rocq version matrix; local success alone does not establish
those remote results.

本地使用 Rocq/coqdoc 9.0.1、OCaml 5.3.0 和 Dune 3.23.1 验证。工具仅依赖
OCaml 标准库（`Unix`、`Str`，要求 OCaml 4.14 或更新版本）及已有 Rocq 工具链。
项目工作流在既有 Rocq 版本矩阵中加入严格示例导出；本地通过不代表远端结果。

Run `dune runtest tools/docs` for filtering, metadata, PDF presentation helpers
and actual coqdoc export regressions, including language separation and proof hiding.
The generator checks output links and anchors on every export.

使用 `dune runtest tools/docs` 运行过滤、元数据、PDF 排版辅助函数与实际 coqdoc
导出回归，涵盖语言分离和证明隐藏。HTML 生成器在每次导出时检查输出链接及锚点。

Future options include Alectryon/Sphinx for interactive proof states and richer
book layout, beyond the current coqdoc HTML and Unicode LaTeX/PDF pipeline.
Automatic conversion of arbitrary Rocq propositions to textbook mathematics
is a separate project.

后续可在现有 coqdoc HTML 和 Unicode LaTeX/PDF 导出基础上，加入 Alectryon/Sphinx
的交互证明状态和更丰富的教材排版。将任意 Rocq 命题自动转换为教材数学排版是
另一项工作。
