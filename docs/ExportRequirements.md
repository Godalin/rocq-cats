# Website and book export requirements

This is the authoritative home for export conventions shared by websites,
HTML reference pages, PDF reading editions and books, in both languages.
Add or revise future presentation requirements here in the same change as
their implementation. Keep commands, dependencies and implementation status
in the [documentation guide](./Documentation.md), linking to these requirements
instead of maintaining competing rules. A requirement does not by itself
claim that every backend already implements it.

Maintain this requirements file in English. Reader-facing source documentation
and exported reading editions remain bilingual.

## Approved visual baseline

Further visual-design iteration is paused at the user-approved presentation.
Apply that presentation by default to the complete English and Chinese PDF
reading editions: approved branding, Pagella prose, JuliaMono code, Fandol
Chinese, restrained blue accents and breakable code frames. The abstract preview
uses the same theme and code-frame implementation; it is a bounded view of the
library, not a separate visual edition. Keep this baseline until the user resumes
visual-design work.

Native proof-state extraction remains optional and separate from the shared
theme. A full-library reading edition must not require Alectryon merely to use
the approved typography and code frames.

## Shared source and native facilities

- Compile and export the entire theory library directly; do not maintain a
  separate tutorial source tree. The preview is the continuous range of complete
  modules in shared reading order from `Cats.Cat.Core` through
  `Cats.Cat.Natural`, inclusive, without fragment selection or a fixed page count.
- Generate both languages from the same compiled Rocq sources and bilingual
  coqdoc comments. Preserve mathematical meaning, specified equality, notation,
  source positions and references. Do not duplicate proofs to suit a renderer.
- Preserve source spelling in code and inline code. Disable coqdoc's implicit
  symbol substitutions, including `*` to `×`, ASCII arrows to Unicode arrows,
  and `forall`/`exists` to quantifier glyphs. Unicode already written in the
  source stays Unicode. Explicit source printing directives remain opt-in.
- Prefer native coqdoc, Alectryon and LaTeX facilities with documented extension
  points. Obtain displayed proof states from Rocq through the supported driver;
  do not invent goals, inject diagnostic commands or parse terminal transcripts
  to construct presentation states.
- Keep proof-state extraction optional and targeted. Ordinary reference exports
  must remain independently buildable; export must not modify shared toolchains.

## Interface explanations

- Place field explanations inside the corresponding interface declaration,
  immediately beside the fields they describe. Interleave code and explanation
  in declaration order, rather than collecting a field catalogue before or
  after the whole interface.
- Keep introductory prose for the mathematical context and overall purpose.
  Explain each field's role, endpoints and relevant laws at its actual use site.
- Use ordinary bilingual coqdoc blocks within the declaration, English first
  and Chinese second. Preserve their native positions in both website and book
  exports; do not duplicate the interface or reconstruct it for presentation.
- Code fragments must not retain leading or trailing blank rows from hidden
  translations or documentation boundaries. Keep nonempty rows' indentation
  and at most one intentional blank row between them; omit empty code frames.

## Constructor bars

For `Inductive` and `CoInductive` constructor lists with an initial `|`, write
`:=| Constructor`: omit the space between `:=` and the first bar, then put one
space after the bar. Use ordinary `| Constructor` syntax for subsequent
branches and align their bars with the first bar in the source. This is a
source-format exception to the ordinary space after
`:=`; export it through native coqdoc without a renderer-specific replacement.

```coq
Inductive ConstructorExample
  : Type
  :=| example_first
    | example_second.
```

PDF code indentation must use the actual space width of its current code font.
Use the native coqdoc indentation command to convert its half-em units to source
spaces, preserving source columns instead of adding constructor-specific padding.

## Section openings

- Introduce every Rocq `Section` with a reader-facing coqdoc heading or opening
  prose, immediately before the section begins. The vernacular `Section` name
  alone is not a reading-edition heading and must not leave a new development
  visually attached to the preceding code.
- Give the mathematical subject a meaningful name. Explain the category,
  objects, functors, chosen structures or other local assumptions fixed by the
  following `Context`, and say which construction or laws are developed next.
  Keep a small context concise; explain changes of assumptions between adjacent
  sections. Do not claim stronger assumptions than the source uses.
- Use native coqdoc heading levels appropriate to the surrounding hierarchy,
  or a short introductory paragraph when it provides enough separation. Keep
  an existing suitable opening rather than adding a duplicate title. A module
  introduction may also introduce its first section when they are adjacent.
- Write separate English-first and Chinese-second comment blocks. Both HTML
  and PDF must retain their native position before the section's context and
  declarations; do not synthesize headings from internal section identifiers
  in the exporter or move assumptions for presentation.

## Learning paths and mathematical diagrams

- Use the shared chapter preferences to keep a learning strand together after
  its prerequisites. Dependency order remains authoritative; a reading preference
  must not hide modules or change mathematical imports merely for presentation.
- For the simplicial strand, introduce ordered shapes, simplicial data, faces
  and degeneracies, standard simplices and low-dimensional nerve examples
  before filling, reconstruction, structural preservation and homotopy results.
  Distinguish an element of one degree from an entire simplicial object, and
  distinguish an illustrative picture from a constructed geometric realization.
- Add prose bridges at conceptual transitions: recall the relevant construction,
  state the new question and refer to the declaration or law that answers it.
  Use native coqdoc references for these links, not hard-coded page numbers.
  Explicit PDF links may use the native LaTeX `\coqref` command around a coqdoc
  identifier, targeting coqdoc's native destination for its qualified declaration.
  Keep the import list as code; explain the mathematical relationship between
  chapters in the prose.
- Place commutative diagrams beside their explanation. Identify the objects and
  arrows, state which equality makes the paths agree, and distinguish a supplied
  arrow from an extension being sought. Dashed arrows indicate requested maps;
  dashed geometric strokes may indicate absent faces only when explained.
- Mathematical diagrams currently target the PDF reading editions. Use native
  TikZ-cd in coqdoc LaTeX islands beside the bilingual mathematical explanation.
  Language-neutral diagrams may use `@lang both`; their explanation remains in
  separate English and Chinese blocks. Avoid TeX percent comments inside islands.
  Defer webpage diagram assets and renderer work until explicitly requested.
- Check the resulting reading order, cross-reference destinations and both
  language editions. Render the changed PDF pages and inspect diagrams for
  incorrect arrows, clipped labels and separation from their explanation.

## Focused proof states

When displaying proof states and a tactic creates multiple goals, **display the
current goal after entering each branch's focus, before the tactics that solve it**.
This applies to `split`, `destruct`, `induction`, constructors and other
branching steps.

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

For example, annotate the focus bullets, not `split`. Alectryon's input-only
block setting keeps unannotated steps as code; the selected bullets reveal
their focused states using its native output controls.

```coq
Proof.
  exists (α ^-1N Hα). split; intros X.
  - (* .unfold .all *)
    exact (fst (Hα X).2).
  - (* .unfold .all *)
    exact (snd (Hα X).2).
Defined.
```

See the [native annotation documentation](https://github.com/cpitclaudel/alectryon#controlling-output-in-literate-documents)
and `NatIso_is_iso` in [Natural.v](../theories/Cat/Natural.v).

## Readability and verification

Use restrained textbook styling, distinguish prose from code, preserve readable
Unicode and Chinese text, and handle long declarations and page breaks without
clipping or isolated frame titles. Keep the approved branding and the shared,
dependency-first reading order. Before claiming a presentation change works,
compile the affected sources and dependents, check both languages, render and
inspect changed PDF pages, and check affected HTML output when implemented.
For branching proofs, verify that each selected output follows its focus and
contains only the current goal, with no output at the unfocused branching step.
Report which backends were actually checked and any remaining limitations.
