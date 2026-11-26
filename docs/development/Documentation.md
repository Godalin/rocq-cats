# Bilingual reading editions

Presentation conventions are maintained in
[ExportRequirements.md](ExportRequirements.md). This guide records build
procedures and implementation status. Reading editions come directly from all
modules under [theories/](../../theories/), using one compiled bilingual source tree.

HTML and both PDF modes disable coqdoc's built-in symbol substitutions with
native `remove printing` directives in generated inputs. Code retains source
spelling, such as `*`, `->` and `forall`; explicit source printing directives
remain available. Native coqdoc show markers retain `Minks.Mixin`,
`Minks.Struct` and `Abbreviation` in the reading editions. The exporter
remaps compiled `.glob` positions and updates the digest for the generated
copy so links can still reach their declarations.

Section openings use native bilingual coqdoc headings or introductory prose.
They identify the local assumptions and the construction or laws that follow;
both backends preserve these openings before the section's context. See the
[section-opening requirements](ExportRequirements.md#section-openings).

PDF uses the native `\coqdocindent` command to convert coqdoc's half-em source
indentation units to the current code font's actual space width. Constructor
bars follow the [shared source convention](ExportRequirements.md#constructor-bars),
so source columns agree with native HTML and PDF output.

## Full-library export

Run from the repository root in the initialized project environment:

```sh
dune exec tools/docs/docs.exe -- pdf --strict
```

The PDFs are `_build/docs-pdf/en/rocq-cats-en.pdf` and
`_build/docs-pdf/zh/rocq-cats-zh.pdf`. All theory modules are discovered
and ordered automatically. Each export first runs
`dune build -j2 @check-library`, without running the Cats test suite, and never
edits tracked Rocq sources. Use the project opam switch locally:

```sh
opam exec --switch=rocq-cats -- dune exec tools/docs/docs.exe -- pdf --strict
```

PDF uses coqdoc LaTeX followed by two XeLaTeX passes with `-no-shell-escape`.
The complete reading editions and abstract preview share the approved theme in
[pdf-textbook.tex](../../tools/docs/pdf-textbook.tex): Pagella prose, JuliaMono
code, Fandol Chinese, quiet blue accents and breakable code frames. It is the
default full-library presentation; further visual-design iteration is paused.
Install JuliaMono Nerd Font with its bold and italic faces; STIX Two Math
supplies fallback symbols.
TeX Live must provide fontspec, geometry, amsmath/amssymb, hyperref, bookmark,
fvextra, newunicodechar, tikz-cd, tcolorbox, titlesec, fancyhdr and TeX Gyre fonts.
The tool does not install dependencies. Locally checked: Rocq/Stdlib 9.2.0,
OCaml 5.3.0, Dune 3.23.1, TeX Live 2025.

The exporter and its compiled-source regression use `rocq compile` and
`rocq doc`, available since Rocq 9.0; legacy `coqc`/`coqdoc` executable aliases
are not required.

For exporter changes, run the focused regressions without exporting the library:

```sh
opam exec --switch=rocq-cats -- dune build -j2 @tools/docs/runtest
```

The compiled [Minks fixture](../../tests/documentation/MinksExport.v), in
`CatsTests.documentation.MinksExport`, checks selected-point computation.
The exporter regression processes its real source and globalization metadata
through both language filters and native coqdoc HTML/LaTeX. It checks visible
Minks commands, generated constructor, parent-view and relative-interface
anchors, and references from actual clients. It also extracts the current
preview proof and checks its two focus annotations. These checks do not run
XeLaTeX or Alectryon.

Both PDF modes normalize coqdoc's native blank-row and indentation markers
before layout and shared code-frame decoration, following the
[code-fragment spacing requirements](ExportRequirements.md#interface-explanations).

## Complete abstract-category preview

The preview uses the same build, language filtering and reading order:

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

The preview uses the full-library theme and shared code-frame decoration.
Cover and contents reuse the full-library template. Source is never rewritten
for layout. References outside the preview are plain text; included declarations
stay linked. The optional native-proof styling is isolated in
[pdf-proof.tex](../../tools/docs/pdf-proof.tex), so the complete PDF needs no
Alectryon installation or proof-style assets.

Only `design` invokes **Alectryon 2.0.0 with the VsRocq driver**, processing the
original context and proof of `nat_iso_is_iso` from
[Natural.v](../../theories/Cat/Natural.v). Native LaTeX replaces that declaration's
code block at its original position; other proofs use ordinary coqdoc hiding.
Native focus-bullet annotations show only each branch's current goal, following
[the focused-state requirements](ExportRequirements.md#focused-proof-states).
There is no diagnostic-command injection, transcript parsing, handwritten goal
or Sphinx build. Generated input, proof, style assets and logs stay in the output
directory and are refreshed each time, without a proof cache.

Install Alectryon on PATH or in this isolated worktree-local environment, which
the exporter finds automatically. The initialized opam environment must supply
compatible `vsrocqtop`. Export never installs dependencies or modifies shared
environments. Ordinary full-library PDF and HTML remain independent of Alectryon.

```sh
uv venv --no-python-downloads _build/docs-alectryon
uv pip install --python _build/docs-alectryon/bin/python 'alectryon==2.0.0'
```

## Authoring and order

Use adjacent, separate coqdoc blocks, English first and Chinese second:

```coq
(** A universal mediator. *)

(**
```

Library imports from compiled `.glob` metadata determine dependency-first
reading order, shared by PDF and HTML. [docs/chapters](../chapters) gives overall
preferences; local lists such as
[theories/Cat/chapters](../../theories/Cat/chapters) refine order. Each optional list
names relative files or directories, one per line. Lists are partial: unlisted
modules stay included; dependencies take precedence. Unknown or repeated entries
fail. A directory may follow an individual file from it without repeating it.
The initial Meta → Set.Core → Set.Morphism → Cat.Core order is automatic.
Each export records its complete order in `reading-order.txt`.

Reference existing declarations in coqdoc brackets. The lexer handles nested
comments and strings, preserves byte positions and newlines, and updates only
generated `.glob` copies after checking source digests. Printing and visibility
directives remain intact. Ambiguous or unpaired prose goes in `warnings.txt`;
`--strict` rejects it. Use `@lang en`, `@lang zh` or `@lang both` when needed.

The new prose bridges use native LaTeX `\coqref` around coqdoc identifiers for
explicit PDF links, for example
`%\coqref{Cats.Instance.Set.Simplicial.Core.simplex restrict}{%[simplex_restrict]%}%`.
Use coqdoc's native destination spelling, where underscores become spaces.
The qualified declaration supplies the destination; the displayed name
remains short. This uses source markup, without changing import handling or
exporter code.

The simplicial learning strand now follows the abstract category introduction:
ordered shapes → simplicial sets → faces and degeneracies → standard simplices
→ nerves and their vertices, edges and spines → boundaries and horns → filling
and matching → reconstruction and finite products → interval and nerve homotopy.
The preferences in [docs/chapters](../chapters) and
[Simplicial/chapters](../../theories/Instance/Set/Simplicial/chapters) keep this strand
ahead of independent STLC, DTT and ETCS directions. General prerequisites still
appear before their clients. The ordinal-nerve comparison follows the interval
chapter because its endpoint compatibility uses that interval interface.

For a first pass, start with the roadmap in
[Ordinal.v](../../theories/Cat/Shape/Ordinal.v), then read the new low-dimensional
explanations in [Core.v](../../theories/Instance/Set/Simplicial/Core.v),
[Operators.v](../../theories/Instance/Set/Simplicial/Operators.v) and
[Standard.v](../../theories/Instance/Set/Simplicial/Standard.v). The prose bridges
refer to the constructions and laws behind each picture. Implementation helpers
and universe transports can be studied on a second pass without losing that
conceptual route. No separate tutorial sources or duplicate proofs are used.

The cover uses the accepted [logo](../branding/rocq-cats.svg); its
[PNG preview](../branding/rocq-cats-preview.png) is copied without conversion.

## Diagrams and checks

Shared coqdoc LaTeX islands can contain native TikZ-cd, already loaded by the
preamble. Avoid TeX percent comments inside the island because percent signs
are coqdoc delimiters. HTML omits these PDF-only islands.

The simplicial chapters use native TikZ-cd inside coqdoc LaTeX islands for PDF
diagrams, marked `@lang both` for language-neutral labels. English and Chinese
explanation blocks identify the paths and their specified equality.
The diagrams cover shape data, restriction composition and naturality, the
standard-simplex element correspondence, nerve composition and functoriality,
boundary versus horn, horn extension, product projections, ordinal comparison,
homotopy endpoints and the natural-transformation prism. Webpage diagrams are
deferred. These are illustrations of the existing checked interfaces; they add no
mathematical definitions or assumptions. See the
[shared requirements](ExportRequirements.md#learning-paths-and-mathematical-diagrams).

`--gallina` hides proofs while retaining declarations and data. Missing glyphs,
overfull boxes, invalid references and damaged bookmark strings fail PDF export.
Inspect `xelatex-output.log` for compiler errors and each language's `.log` for
layout diagnostics. All generated files stay under the output directory.
Run `dune runtest tools/docs` for lexical, position, reading-order and real
coqdoc export tests. For visual review, use
`mutool draw -r 120 -o page-%d.png document.pdf`.

Basic HTML remains available with
`dune exec tools/docs/docs.exe -- build --strict`, opening `_build/docs/index.html`.
It retains coqdoc styling, indices and contents, language/source links and checked
local destinations. Native proof-state integration currently targets the PDF preview.
