# Bilingual reading editions

# 双语阅读版

The current priority is PDF for personal study. One bilingual Rocq source tree
supplies both languages: reference modules in [theories/](../theories/) and
the checked tutorial chapters in [book/](../book/). One PDF per language
contains the entire library and its tutorials. Examples compile with
the library. The full-library PDF cover uses the accepted
[Rocq-Cats logo](./branding/rocq-cats.svg).

当前优先支持个人学习用的 PDF。一套双语 Rocq 源码提供两种语言：参考模块位于
[theories/](../theories/)，经过检查的教程章节位于 [book/](../book/)。每种语言的一本
PDF 包含全库与教程。示例与库一起编译，封面使用已确认的
[Rocq-Cats Logo](./branding/rocq-cats.svg)。

## Build / 构建

Run from the repository root with the initialized project toolchain:

在仓库根目录中，使用已初始化的项目工具环境运行：

```sh
dune exec tools/docs/docs.exe -- pdf --strict
```

The English and Chinese PDFs are written to
`_build/docs-pdf/en/rocq-cats-en.pdf` and
`_build/docs-pdf/zh/rocq-cats-zh.pdf`. There is a single full-library export;
tutorials are included, rather than exported as a second book.
Each export first runs `dune build @all` and never edits tracked Rocq sources.

英文和中文 PDF 分别写入 `_build/docs-pdf/en/rocq-cats-en.pdf` 和
`_build/docs-pdf/zh/rocq-cats-zh.pdf`。只有一个全库导出入口，教程直接编入同一本书。
每次导出先运行 `dune build @all`，
不会修改受版本管理的 Rocq 源码。

For the local Nix/opam environment:

本地 Nix/opam 环境使用：

```sh
opam exec --switch=rocq-env -- nix-shell --run \
  'dune exec tools/docs/docs.exe -- pdf --strict'
```

PDF uses coqdoc LaTeX output followed by two XeLaTeX passes, with
`-no-shell-escape`. Install JuliaMono Nerd Font for Latin prose, headings and
code, including its bold, italic and bold italic faces. XeLaTeX resolves it by
the installed family name `JuliaMono Nerd Font`. TeX Live must provide
CTeX/Fandol for Chinese, STIX Two Math for fallback symbols,
fontspec, geometry, amsmath/amssymb, hyperref, bookmark, fvextra, newunicodechar
and tikz-cd. The tool does not install dependencies.
Locally checked: Rocq/coqdoc 9.0.1, OCaml 5.3.0,
Dune 3.23.1, TeX Live 2025 / XeTeX 0.999997.

PDF 使用 coqdoc 的 LaTeX 输出，再以 `-no-shell-escape` 运行两次 XeLaTeX。
西文正文、标题和代码使用 JuliaMono Nerd Font，需安装其常规、粗体、斜体及粗斜体。
XeLaTeX 按已安装的字体家族名称 `JuliaMono Nerd Font` 定位。
TeX Live 需提供中文字体 CTeX/Fandol、备用符号字体 STIX Two Math、fontspec、geometry、
amsmath/amssymb、hyperref、bookmark、fvextra、newunicodechar 和 tikz-cd。
工具不会安装依赖。本地验证版本：
Rocq/coqdoc 9.0.1、OCaml 5.3.0、Dune 3.23.1、TeX Live 2025 / XeTeX 0.999997。

## Authoring / 写作

Use adjacent, separate coqdoc blocks, English first and Chinese second:

使用相邻且分开的 coqdoc 注释块，先英文后中文：

```coq
(** A universal mediator. *)

(** 泛中介。 *)
```

Code, examples and proofs are shared. Add executable examples directly to a
chapter; Dune compiles them. Every module and tutorial is discovered
automatically. The exporter uses library imports from the compiled `.glob`
metadata to produce a dependency-first reading order, shared by PDF and HTML.

代码、示例与证明共享。将可执行示例直接加入章节，Dune 负责其编译。所有模块和
教程均自动发现，导出器读取编译生成的 `.glob` 导入记录，按依赖优先编排阅读顺序，
PDF 与 HTML 共享这份顺序。

[docs/chapters](./chapters) expresses overall preferences;
[theories/Cat/chapters](../theories/Cat/chapters) and
[book/chapters](../book/chapters) refine local order. Each optional `chapters`
file lists relative filenames or directories, one per line. Lists are partial:
unlisted modules are still included. Dependencies take precedence over these
preferences. Unknown or repeated entries fail; a directory entry can follow
an individual file from that directory without repeating the file.

[docs/chapters](./chapters) 表达整体偏好；
[theories/Cat/chapters](../theories/Cat/chapters) 与
[book/chapters](../book/chapters) 调整局部顺序。任意目录中可选的 `chapters` 文件
按行列出相对文件名或目录，只需列出要调整的部分，未列出的模块仍自动纳入。
依赖优先于手工偏好。未知或重复条目会报错；可以先列目录内的某个文件，再列
整个目录，导出不会重复该文件。

All imports precede their clients, without entry-point exceptions. The initial
sequence `Meta`, `Set.Core`, `Set.Morphism`, `Cat.Core` follows automatically
from dependencies; no manual list is needed for these foundations. The
generated `reading-order.txt` records the complete order next to each export.

所有导入均先于使用者，不设置阅读入口例外。开头的 `Meta`、`Set.Core`、
`Set.Morphism`、`Cat.Core` 顺序由依赖自动得到，这些基础无需手工指定。
每份导出目录中的 `reading-order.txt` 记录完整顺序。

Reference existing declarations in coqdoc brackets instead of duplicating proofs.
The tutorial starts with [Basics.v](../book/Basics.v), following one Boolean
example from categories through functors, natural transformations and products
to limits. [STLC.v](../book/STLC.v) continues with typed syntax, substitution,
beta/eta equality and CCC semantics, then explains the existing syntactic
categories, equational completeness and free universal property. Its examples
reuse library definitions and theorems. The [SVG](./branding/rocq-cats.svg)
is the editable logo source; its
[PNG preview](./branding/rocq-cats-preview.png) is copied into the PDF output
for the cover, with no additional image-conversion dependency.

通过 coqdoc 括号引用已有声明，无需复制证明。教程从
[Basics.v](../book/Basics.v) 开始，用同一个布尔例子串起范畴、函子、自然变换、积与极限。
[STLC.v](../book/STLC.v) 继续讲解带类型语法、替换、βη 相等与 CCC 语义，再介绍
已有的语法范畴、等式完备性与自由泛性质；示例复用库中的定义与定理。
[SVG](./branding/rocq-cats.svg) 是可编辑 Logo 源文件；封面直接使用复制到 PDF
输出目录的 [PNG 预览](./branding/rocq-cats-preview.png)，不增加图片转换依赖。

The lexer handles strings and nested comments, preserves every byte position and
newline, and updates only generated `.glob` copies after checking the source
digest. Printing/visibility directives remain intact. Ambiguous or unpaired
prose is reported in `warnings.txt`; `--strict` rejects it. Explicit `@lang en`,
`@lang zh` or `@lang both` markers are available when pairing does not apply.

词法过滤器识别字符串和嵌套注释，保留每个字节位置及换行，检查源码校验值后仅
更新生成的 `.glob` 副本。打印和显隐指令保持原样。歧义或未配对的文字记录到
`warnings.txt`，`--strict` 将其视为失败。不适用翻译配对时，可显式使用
`@lang en`、`@lang zh` 或 `@lang both` 标记。

## Commutative diagrams / 交换图

Write native TikZ-cd in a shared coqdoc LaTeX island. Mathematical labels use
ordinary LaTeX; the preamble already loads tikz-cd. Keep the island free of TeX
percent comments, since percent signs delimit the coqdoc island.

在共享 coqdoc LaTeX 片段中直接写 TikZ-cd，数学标签使用普通 LaTeX；模板已加载
tikz-cd。片段中避免 TeX 百分号注释，因为百分号用于界定 coqdoc 片段。

```coq
(** @lang both
%
\[
\begin{tikzcd}
  A \arrow[r, "f"] & B
\end{tikzcd}
\]
%
*)
```

Both language PDFs use this same diagram source. The introductory chapter
contains a product diagram with its unique mediator.
The existing HTML backend omits these PDF-only LaTeX islands;
the surrounding bilingual explanations and equations remain readable.

两种语言的 PDF 使用同一份图源。入门章节包含带唯一中介的积图式。
已有 HTML 后端忽略这些 PDF 专用 LaTeX 片段，周围的双语说明
和方程仍可阅读。

## Checks and output / 检查与输出

`--gallina` hides proofs while retaining declarations and data. Generated TeX,
filtered inputs, original source copies and logs stay under the output directory.
Missing glyphs, overfull boxes, invalid references and broken bookmark strings
fail PDF export. Inspect `xelatex-output.log` for compiler errors and the
language-specific `.log` for layout diagnostics. Changed inputs invalidate only
the generated TeX auxiliary files. This is a coqdoc reading edition, not semantic
conversion of arbitrary Rocq formulas into conventional mathematics.

`--gallina` 隐藏证明，保留声明及数据。生成的 TeX、过滤输入、原始源码副本和日志
均位于输出目录下。缺字、版面溢出、无效引用及损坏书签会使 PDF 导出失败。编译
错误见 `xelatex-output.log`，排版诊断见对应语种的 `.log`。输入变化时仅使生成的
TeX 辅助文件失效。这是 coqdoc 阅读版，不会对任意 Rocq 公式进行语义转换。

Run `dune runtest tools/docs` for lexical/position checks, PDF presentation
helpers and actual coqdoc HTML/LaTeX export tests. They require no TeX renderer.
For visual review, render selected PDF pages with MuPDF, for example
`mutool draw -r 120 -o page-%d.png document.pdf`.

运行 `dune runtest tools/docs` 检查词法、位置、PDF 排版辅助函数和实际 coqdoc
HTML/LaTeX 导出，无需 TeX 渲染器。视觉检查可使用 MuPDF，例如
`mutool draw -r 120 -o page-%d.png document.pdf`。

Basic HTML export remains available with
`dune exec tools/docs/docs.exe -- build --strict`, opening `_build/docs/index.html`.
It uses coqdoc's own stylesheet,
index and contents, plus language/source links and checked local destinations.

基础 HTML 仍可通过 `dune exec tools/docs/docs.exe -- build --strict` 导出，入口为
`_build/docs/index.html`，使用 coqdoc 自带样式、索引和目录，保留语言与源码链接，
并检查本地跳转目标。
