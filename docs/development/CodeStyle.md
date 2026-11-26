# Rocq source layout

These conventions capture repeated reviewed formatting in
[Cat/Natural.v](../../theories/Cat/Natural.v),
[Cat/Adjunction.v](../../theories/Cat/Adjunction.v) and
[Cat/ProductPullback.v](../../theories/Cat/ProductPullback.v).
Group code by its mathematical and proof structure. About 80 columns is
a readability guide, not a reason to pack every short declaration or to
split every argument onto a separate line. Preserve the reviewed local
layout; do not turn isolated inconsistencies into general rules.

For the choice of parameters and components, see the
[mathematical interface guide](HierarchyDevelopment.md).

## Declaration groups

List the modules of a grouped `Require Import` or `Require Export` below the
command, one per line. Group imports by their role and use `Export` for the
parent interface that clients should inherit.

Keep the ambient categories or structures near the declaration name.
Group dependent functors, objects and morphisms by role; related implicit
and explicit binders may share a line. Ordinary declaration parameter
continuations use four spaces; continued `Context` groups use two.
A declaration may benefit from these groups even when it fits on one line.

```coq
Definition HCompN {C D E : Cat}
    {G G' : Fct D E} {F F' : Fct C D}
    (β : G ⇒ G') (α : F ⇒ F')
  : (G ∘F F) ⇒ (G' ∘F F')
  := (β ∘Nr F') ∘Nv (G ∘Nl α).

Context {C D : Cat}
  {F : Fct C D} {G : Fct D C}
  (A : F ⊣ G).
```

In `Arguments` declarations use `_` for argument slots, keeping the braces,
scopes and reduction marks that give the declaration its meaning. At a call
site a named argument such as `(obj := F)` can identify the needed datum.
For example, `Arguments hasMonoidObj {_ _} _.` leaves the bundle explicit.

## Minks declarations

Start the `extends` clause of `Minks.Mixin` and `Minks.Struct` on a
new line, indented two spaces from the declaration. Keep the first parent
on that line. If the parent list wraps, break after a comma and align the
continuation with the first parent.

Leave two spaces after `with` and align subsequent components with the first. Start
`exports` on its own line and align continued exports with the first name.
Keep a short field application together; a long application can start on
the following indented line with its `:`.

```coq
Minks.Struct SymPremonoidalCat
  extends PremonoidalCat
  with  hasTensorSym : HasTensorSym,
        isSymHexagon : IsSymHexagon,
        isSymUnit : IsSymUnit
  exports HasSymPremonoidal [carrier].

Minks.Struct MonoidalCat
  extends SemigroupalCat, PremonoidalCat
  exports HasMonoidal [carrier].
```

## Types and terms

Start the result-type `:` and definition-body `:=` on separate lines,
each indented two spaces. Split a long result at an equation, connective
or complete argument boundary. Indent a nested argument one further level;
avoid large padding merely to align with the width of a keyword.

Keep a short equation on one line. When the two sides need separate lines,
start the continuation with `=`, `≈`, or the applicable equality notation.
Keep a pair, bracket notation or a short application together. For a chain of
compositions, break before `∘` and group the factors by their role.
The body starts immediately after `:=`, except for a record opening on the
next line. An `Inductive` or `CoInductive` with an initial bar starts with
`:=| Constructor`; align later constructor bars with that bar.

```coq
assert (H : ⟨const[Y2] (f x), id⟩ ∘ g
  ≈ (f × g) ∘ ⟨const[X2] x, id⟩).
```

```coq
Global Instance nat_whisker_l_proper {C D E : Cat}
    (G : Fct D E) {F F' : Fct C D}
  : Proper (NatEq ==> NatEq)
      (@WhiskerLN C D E G F F').

Theorem adj_unit_universal {X Y} (g : Hom X (G Y))
  : is_unique (λ f, fmap G f ∘ adj_unit X ≈ g)
      (unadjunct g).
```

## Proof steps

Keep short steps belonging to one phase together, such as
`intros X. exists id.`. Split before a longer `change`, `exact`,
`apply` or a new proof phase. Use two-space proof nesting; do not build
column alignment around the spelling or width of a bullet. Wrap long
`rewrite` lists at commas, retaining coherent groups of laws together.

```coq
Next Obligation. intros X. exists id.
  split; cbn; apply comp_id_l.
Defined.
```

A whole short proof can remain `Proof. ... Qed.` or a one-line obligation.
Once the body spans lines, put `Qed.` or `Defined.` on its own line.
The first short step may stay after `Proof.` or `Next Obligation.`;
one tactic per line is not compulsory.

## Proof transparency

Use `Qed` for laws whose statements suffice to use them. This includes
`Proper`, preservation of identities and composition, naturality, coherence,
and universal-property equations or uniqueness proofs used to rewrite.
With `Program`, close these obligations individually and keep the enclosing
structure transparent when its data projections compute.

Use `Defined` for functions and witnesses whose bodies consumers need to
reduce, such as inverse arrows, mediators, preimages, and selected data
projected from `sig` or `sigT`. Classify the particular obligation by how it
is used. A `Type`-valued Hom equality may serve solely as a rewrite rule.
A proof in `Prop` may still drive dependent transport or be needed for
conversion or guardedness. Document such a dependency near the proof and
check the affected reduction or client.

Audit transparency changes in small batches. Build affected consumers and
exercise relevant rewriting, instance search, strict universes and concrete
reduction. Compare timing with the same targets, toolchain and cache
conditions. Keep `Unset Transparent Obligations` experiments local and
verify which automatically solved obligations still need reduction.
See [issue #47](https://github.com/Godalin/rocq-cats/issues/47).

## Notation and records

Use brackets when a public term notation takes a selected object, boundary
or other explicit data. Keep Rocq's `@` for explicit application of a name.
For ordinary term `Notation`, `Infix` and `Reserved` grammar, write the
precedence explicitly. Open `(at level …)` on its own line with two spaces
of indentation. Break a long list of modifiers at commas and indent its
continuation two more spaces. A scope starts on a separate line at two
spaces, with the colon at the start of that line. Keep a short interpretation
on the declaration line. For a long one, break before `:=` and indent it two
spaces, with the interpretation beginning immediately after `:=`.
Numeral and string notations use Rocq's primitive grammar. Give them a scope
without a precedence modifier. Named abbreviations and tactic notation use
their own grammar. A record field's `where` interpretation uses the
precedence in its reserved grammar.
Use level 0 for closed bracket notation and level 1 for new projection-like
postfix notation. For an existing precedence, group terms explicitly when
needed to avoid Rocq's deprecated level tolerance.

```coq
Notation "'id[' X ']'" := (@id _ X)
  (at level 0, format "id[ X ]")
  : hom_scope.

Infix "∘Nh" := HCompN
  (at level 50, left associativity)
  : cat_scope.
```

For record literals, keep named fields, the first field immediately after
`{|`, and aligned `;` and `|}`. Put a multiline record's closing delimiter on
its own line. Prefer a short constructor for a single-field wrapper.

Use public notation for operations in statements, terms and proofs. Put it in
the module introducing the operation; inherit it through the appropriate
export. A short `where` following a record field makes reserved notation
available in subsequent fields. Declare its public interpretation once after
the record. Break a field-local scope onto the next line, indented two spaces
beyond `where` or `and`. Keep postfix notation tight in use, e.g. `C^op`.
Resolve precedence warnings at their declaration; scope a warning attribute
to the individual notation when the chosen precedence requires it.

## Object and morphism products

In functor/product theory that mixes object and morphism products, put
`Local Open Scope ob_scope.` after the other local scope openings. This
lets a coerced functor application such as `F (X × Y)` use object notation.
The existing argument scopes of `fmap`, composition and hom equality select
morphism notation for their arrow arguments, so the same formula can use
both products without explicit delimiters. Keep this default local to the
module or section; importing the theory retains the caller's scope choices.

```coq
Local Open Scope ob_scope.

Definition mapped_product {C D : Cat} `{PC : !HasProduct C}
    (F : Fct C D) {X Y X' Y' : C}
    (f : Hom X X') (g : Hom Y Y')
  : Hom (F (X × Y)) (F (X' × Y'))
  := fmap F (f × g).
```

The tensor notation `⊗` follows the same object and morphism scope rule.
For example, `F (X ⊗ Y)` uses the chosen object tensor, while
`fmap F (f ⊗ g)` uses the corresponding joint arrow map.
An isolated `Check (f ⊗ g)%hom` requests the arrow interpretation.

A bare morphism product outside an argument with a known hom scope may
still need `%hom`. Give new operation arguments their mathematical scopes
through their types or `Arguments`, and keep bundle-owned choices explicit
where multiple choices share a category. Scope defaults choose notation;
the supplied terminal/product evidence still determines the construction.

Use separate English and Chinese coqdoc blocks in `theories/`. Write test,
configuration and tooling comments in English. Keep blank lines around comments. Apply layout changes to the requested region, rather than
reflowing unrelated source while editing mathematics. Settle formatting
before expensive validation, following [the testing guide](Testing.md).
