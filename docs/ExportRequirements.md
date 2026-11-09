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

## Shared source and native facilities

- Compile and export the entire theory library directly; do not maintain a
  separate tutorial source tree. The preview is the continuous range of complete
  modules in shared reading order from `Cats.Cat.Core` through
  `Cats.Cat.Natural`, inclusive, without fragment selection or a fixed page count.
- Generate both languages from the same compiled Rocq sources and bilingual
  coqdoc comments. Preserve mathematical meaning, specified equality, notation,
  source positions and references. Do not duplicate proofs to suit a renderer.
- Prefer native coqdoc, Alectryon and LaTeX facilities with documented extension
  points. Obtain displayed proof states from Rocq through the supported driver;
  do not invent goals, inject diagnostic commands or parse terminal transcripts
  to construct presentation states.
- Keep proof-state extraction optional and targeted. Ordinary reference exports
  must remain independently buildable; export must not modify shared toolchains.

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
