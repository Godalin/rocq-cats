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

## Validation and scope / 验证与范围

Locally validated with Rocq/coqdoc 9.0.1, OCaml 5.3.0 and Dune 3.23.1. The tool
uses only OCaml standard libraries (`Unix`, `Str`; OCaml 4.14 or newer) and the
existing Rocq toolchain. The project workflow also runs the strict sample export
in its existing Rocq version matrix; local success alone does not establish
those remote results.

本地使用 Rocq/coqdoc 9.0.1、OCaml 5.3.0 和 Dune 3.23.1 验证。工具仅依赖
OCaml 标准库（`Unix`、`Str`，要求 OCaml 4.14 或更新版本）及已有 Rocq 工具链。
项目工作流在既有 Rocq 版本矩阵中加入严格示例导出；本地通过不代表远端结果。

Run `dune runtest tools/docs` for filtering, metadata and actual coqdoc export
regressions, including language separation and proof hiding.
The generator checks output links and anchors on every export.

使用 `dune runtest tools/docs` 运行过滤、元数据与实际 coqdoc 导出回归，涵盖语言
分离和证明隐藏。生成器在每次导出时检查输出链接及锚点。

Future options include Alectryon/Sphinx for interactive proof states and richer
book layout, and a separately configured Unicode-capable LaTeX/PDF pipeline.
Automatic conversion of arbitrary Rocq propositions to textbook mathematics
is a separate project.

后续可加入 Alectryon/Sphinx 的交互证明状态和更丰富的教材排版，以及独立配置的
Unicode LaTeX/PDF 导出。将任意 Rocq 命题自动转换为教材数学排版是另一项工作。
