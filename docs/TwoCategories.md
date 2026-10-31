# Two-dimensional structure and equality

This is the first boundary experiment for [issue #14](https://github.com/Godalin/rocq-cats/issues/14).
It retains all 2-cells and specifies their composition and coherence explicitly.

## The interface

[Bicategory.v](../theories/Cat/Bicategory.v) defines a single class `Bicat`,
containing objects, hom-categories, composition, and coherence:

| Level | Data | Comparison |
| --- | --- | --- |
| 0-cells | `ObB` | No object equality is added |
| 1-cells from `X` to `Y` | Objects of `HomCat X Y` | Isomorphisms are explicit 2-cell data |
| 2-cells from `f` to `g` | Morphisms of `HomCat X Y` | `CellEq`, the hom-category's `HomEq` |

Identity 1-cells are chosen. Composition is a functor
`HomCat Y Z × HomCat X Y → HomCat X Z`. Thus vertical composition comes from
the hom-categories, and horizontal composition preserves identities,
composition (the interchange law), and equivalence of parallel 2-cells.
Whiskering is derived from horizontal composition with identity 2-cells.

In `bicat_scope` (`%bicat`), the notation is `f ⇒₂ g`, `α ≈₂ β`, `g ∘₁ f`,
`β ∘₂ α`, `β ⋆ α`, `𝟙₁ X`, `𝟙₂ f`, `g ◁ α`, and `β ▷ f`.
Parentheses distinguish vertical and horizontal composition in mixed expressions.

The same class contains specified invertible associators and left/right
unitors, their naturality, and the pentagon and triangle equations. These equations use
`CellEq`. Merely allowing 1-cells to be isomorphic would not provide this data
or these coherence proofs.

The cell types and composition operations are derived fields, not additional
choices or a separate data structure. Model structures remain transparent
definitions and are enabled explicitly, for example with
`Local Existing Instance CatBicat`.

The interface uses explicit associators and unitors rather than native Rocq
equalities of 1-cells. A separate notion of strictness is left for future
design; it is not inferred merely from invertibility of the comparison cells.

All structures are universe-polymorphic, but the four conceptual levels do
not currently have four independent size levels. Inspection of the generated
types shows that the existing `Functor` and `ProdCat` interfaces accept
categories whose `Hom` and `HomEq` levels coincide. Consequently `Bicat`
has `HomCat : ObB → ObB → Cat@{h t t}`: 2-cells and their equivalence witnesses
share a universe. The concrete `CatBicat` also uses a common size bound
for its 1-cells and 2-cells. Auxiliary universes and their upper-bound
constraints are inferred; the object universe of the category model is
strictly above the represented categories' component levels.

This is an explicit inherited size restriction, not a resizing theorem.
Removing it requires a separate audit of the existing polymorphic relation,
product-category and functor interfaces. It is not repaired by declaring a
universe of all categories at its own level.

## Categories, functors, and natural transformations

[Natural.v](../theories/Cat/Natural.v) provides horizontal composition `β ∘Nh α`
and proves the two component formulas equivalent by naturality:

```text
β_(F' X) ∘ G(α_X) ≈ G'(α_X) ∘ β_(F X).
```

It proves interchange and packages composition as `CompNF`, a functor on the
two functor categories. Horizontal composition also preserves natural
isomorphisms, with computational inverse witnesses.

[CatBicat.v](../theories/Cat/CatBicat.v) instantiates `Bicat` with `Cat`,
`Fct C D`, `IdF`, and `CompNF`. The same structure supplies the canonical identity-
component associators and unitors and proves all coherence laws. All natural
transformations are 2-cells, including noninvertible ones; parallel 2-cells
are compared by `NatEq`. Derived whiskering agrees with the existing
`∘Nl` and `∘Nr` operations up to `NatEq`.

This is a bicategory presentation of the example. The usual mathematical
2-category of categories is strict on functor actions. In the current Rocq
representation, functors also contain `Type`-valued law witnesses. The actions
of `IdF ∘F F` and `F`, or the two parenthesizations of a triple composite,
agree definitionally, but their full records are not definitionally equal.
No native record-equality theorem is claimed. This is a representation
boundary, not a theorem that an axiom-free
strict presentation is impossible. An alternative presentation or a further
explicit extensionality result would need a separate investigation.

The existing [CatCat.v](../theories/Cat/CatCat.v) is a separate one-dimensional
shadow: functors are arrows and natural isomorphisms are their equivalence
witnesses. Its object isomorphisms are equivalences with chosen quasi-inverses.
It does not replace `CatBicat` or its noninvertible 2-cells. A general shadow
construction for arbitrary bicategories is left for later.

## An additive example with noninvertible 2-cells

[Instance/Nat/TwoCat.v](../theories/Instance/Nat/TwoCat.v) has one 0-cell, one
1-cell, and natural numbers as 2-cells. Both compositions add natural numbers;
commutativity gives interchange. The theorem `nat_2cell_not_iso` shows that
positive 2-cells are not invertible, so the example does not restrict its
hom-category to a groupoid.

## What this experiment establishes

The existing setoid-based category interface can serve as hom-categories for
constructive two-dimensional composition and bicategory coherence. The highest
comparison remains a `Type`-valued equivalence relation. Its witnesses are not
provided with a 3-category's compositions and coherence, so this experiment
does not establish a general framework for arbitrary higher categories.

Validation uses full-library compilation and temporary computation, notation,
and assumption checks; no routine permanent tests or `Print Assumptions`
commands are added to the library. Compatibility with the supported Rocq
versions is checked by the CI matrix.
