# Bilingual reading editions

# 双语阅读版

The current priority is PDF for personal study. One bilingual Rocq source tree
supplies both languages: reference modules in [theories/](../theories/) and
the checked introductory chapter in [book/](../book/). Examples compile with
the library. The tutorial PDF cover uses the accepted
[Rocq-Cats logo](./branding/rocq-cats.svg).

当前优先支持个人学习用的 PDF。一套双语 Rocq 源码提供两种语言：参考模块位于
[theories/](../theories/)，经过检查的入门章节位于 [book/](../book/)。示例与库一起编译，
教程 PDF 封面使用已确认的 [Rocq-Cats Logo](./branding/rocq-cats.svg)。

## Build / 构建

Run from the repository root with the initialized project toolchain:

在仓库根目录中，使用已初始化的项目工具环境运行：

```sh
dune exec tools/docs/docs.exe -- pdf --book --strict
```

The English and Chinese PDFs are written to
`_build/docs-pdf/book/en/rocq-cats-en.pdf` and
`_build/docs-pdf/book/zh/rocq-cats-zh.pdf`. Omit `--book` for the full theory
reference and tutorials, under `_build/docs-pdf/full/` with the same layout.
Each export first runs `dune build @all` and never edits tracked Rocq sources.

英文和中文 PDF 分别写入 `_build/docs-pdf/book/en/rocq-cats-en.pdf` 和
`_build/docs-pdf/book/zh/rocq-cats-zh.pdf`。省略 `--book` 可导出完整理论参考和教程，
输出位于 `_build/docs-pdf/full/`，布局相同。每次导出先运行 `dune build @all`，
不会修改受版本管理的 Rocq 源码。

For the local Nix/opam environment:

本地 Nix/opam 环境使用：

```sh
opam exec --switch=rocq-env -- nix-shell --run \
  'dune exec tools/docs/docs.exe -- pdf --book --strict'
```

PDF uses coqdoc LaTeX output followed by two XeLaTeX passes, with
`-no-shell-escape`. TeX Live must provide CTeX/Fandol, DejaVu, STIX Two Math,
fontspec, geometry, amsmath/amssymb, hyperref, bookmark, fvextra, newunicodechar
and tikz-cd. Fonts use TeX filenames rather than OS-specific names. The tool
does not install dependencies. Locally checked: Rocq/coqdoc 9.0.1, OCaml 5.3.0,
Dune 3.23.1, TeX Live 2025 / XeTeX 0.999997.

PDF 使用 coqdoc 的 LaTeX 输出，再以 `-no-shell-escape` 运行两次 XeLaTeX。
TeX Live 需提供 CTeX/Fandol、DejaVu、STIX Two Math、fontspec、geometry、
amsmath/amssymb、hyperref、bookmark、fvextra、newunicodechar 和 tikz-cd。
字体使用 TeX 文件名，不依赖操作系统专用名称；工具不会安装依赖。本地验证版本：
Rocq/coqdoc 9.0.1、OCaml 5.3.0、Dune 3.23.1、TeX Live 2025 / XeTeX 0.999997。

## Authoring / 写作

Use adjacent, separate coqdoc blocks, English first and Chinese second:

使用相邻且分开的 coqdoc 注释块，先英文后中文：

```coq
(** A universal mediator. *)

(** 泛中介。 *)
```

Code, examples and proofs are shared. Add executable examples directly to a
chapter; Dune compiles them and the exporter discovers the chapter automatically.
Reference existing declarations in coqdoc brackets instead of duplicating proofs.
The tutorial retains only [Basics.v](../book/Basics.v), following one Boolean example
from categories through functors, natural transformations and products to
limits. The [SVG](./branding/rocq-cats.svg) is the editable logo source; its
[PNG preview](./branding/rocq-cats-preview.png) is copied into the PDF output
for the cover, with no additional image-conversion dependency.

代码、示例与证明共享。将可执行示例直接加入章节，Dune 负责其编译，导出器自动
发现章节。通过 coqdoc 括号引用已有声明，无需复制证明。教程仅保留
[Basics.v](../book/Basics.v)，用同一个布尔例子串起范畴、函子、自然变换、积与极限。
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
