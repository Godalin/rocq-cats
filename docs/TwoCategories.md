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
| 2-cells from `f` to `g` | Morphisms of `HomCat X Y` | `Cell2Eq`, the hom-category's `HomEq` |

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
`Cell2Eq`. Merely allowing 1-cells to be isomorphic would not provide this data
or these coherence proofs.

The cell types and composition operations are derived fields, not additional
choices or a separate data structure. Model structures remain transparent
definitions and are enabled explicitly, for example with
`Local Existing Instance CatBicat`.

The interface uses explicit associators and unitors rather than native Rocq
equalities of 1-cells. Strictness relative to a specified 1-cell setoid is
provided separately below; it is not inferred merely from invertibility of
the comparison cells.

## Universe audit

The four cell/equality sizes are independent. The earlier coupling came from
`Cat@{o h p | h <= p}`: when a bare `Cat` was instantiated with fresh
universes, Rocq's minimization identified `h` with its bound `p`. Even
`Definition keep_cat (C : Cat) := C` acquired the restricted argument type
`Cat@{o h h}`. This was not a restriction intrinsic to `Functor`, `ProdCat`
or two-dimensional composition. See the reference manual's
[minimization and explicit universes](https://docs.rocq-prover.org/master/refman/addendum/universe-polymorphism.html#minimization).

`Cat@{o h p +}` now leaves morphisms in `Type@{h}` and their equivalence
witnesses in `Type@{p}`, with larger auxiliary universes for law witnesses.
The inferred signature on Rocq 9.0.1 is `Cat@{o h p l q}`, with
`h <= q`, `p <= q`, and `q <= l` (and their redundant consequences).
There is no required inequality between `h` and `p`. `Functor`, `ProdCat`
and `Fct` consequently retain separate morphism and equality sizes without
changes to their mathematical fields. Their auxiliary upper bounds remain.

`Bicat@{o h t p +}` explicitly names the universes of 0-cells, 1-cells,
2-cells, and 2-cell equality witnesses. The actual inferred instance is
`Bicat@{o h t p a b l}`, with:

```text
ObB      : Type@{o}
Cell1    : ObB → ObB → Type@{h}
Cell2    : Cell1 X Y → Cell1 X Y → Type@{t}
Cell2Eq  : Cell2 f g → Cell2 f g → Type@{p}
HomCat   : ObB → ObB → Cat@{h t p l l}

p < a <= b,   t <= b,   t <= l,   p <= l
```

The generated constraints also retain the product/projection bounds
`h, t <= projections.u0, projections.u1` and `p <= prod.u1`; these are
upper bounds from the existing product machinery, not equations between
the four cell levels. The `CatBicat` signature likewise no longer equates
its 1-cell, 2-cell and equality universes. Its category-object universe
still lies strictly above the sizes of the represented categories.

Temporary checks instantiate identity functors, product categories and
functor categories with both `h < p` and `p < h`; a transparent natural-number
category also has independently specified `h` and `p`. The bicategory
interface accepts both `o < h < t < p` and the reversed ordering. No resizing
axiom or universe containing itself is used.

## Strictness relative to a 1-cell setoid

[TwoCategory.v](../theories/Cat/TwoCategory.v) defines `IsStrictTwoCat K R cmp`
for a bicategory `K`, a specified `Type`-valued relation `R` on parallel
1-cells, and comparison 2-cells `cmp p : f ⇒₂ g` for `p : f ≈₁[R X Y] g`.
The class requires:

- `R` is an equivalence, and composition of 1-cells respects it.
- Every equality loop acts as an identity 2-cell. Comparisons respect vertical
  and horizontal composition, independently of the chosen relation witnesses.
- Composition is associative and unital under `R`.
- The bicategory's specified associators and unitors agree, under `≈₂`, with
  the comparisons induced by those associativity and unit witnesses.

Thus the 1-cell laws use `≈₁[R X Y]`, and the comparison laws use `≈₂`. There is
no native equality of 1-cells in this interface. The derived theorem
`cell1_eq_to_cell2_unique` identifies the actions of any two witnesses of the
same relation, without identifying the witnesses themselves.
`cell1_eq_to_cell2_iso` constructs the inverse comparison from the symmetry
witness; its inverse map remains computational.

The comparisons provide transport between representatives: a 2-cell
`α : f ⇒₂ g` can be moved to `f' ⇒₂ g'` by composing with the comparison
for `g ≈₁[R X Y] g'` on the left and the inverse comparison for `f ≈₁[R X Y] f'`
on the right. This makes the change of endpoints explicit instead of
comparing nonparallel 2-cells directly.

This is strictness **relative to the supplied setoid presentation**. It does
not assert definitional or native equality of representatives, nor construct
a quotient or a strictification. Taking arbitrary invertible 2-cells as
equality witnesses with their underlying maps as comparisons does not in
general satisfy the interface: a nonidentity automorphism would violate the
equality-loop law. No such structure for `CatBicat` is claimed here.

The designated setoid equality is the mathematical equality of this library.
Accordingly the interface remains named `IsStrictTwoCat`: it expresses the
intended strictness, without adding native equality of representatives as a
further requirement.

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

## The one-dimensional shadow

[BicatHomotopy.v](../theories/Cat/BicatHomotopy.v) defines
`BicatHomotopyCat K`. Its objects and arrows are the 0-cells and 1-cells of
`K`; arrow equivalence is isomorphism in the corresponding hom-category.
Horizontal composition preserves this relation because `comp1F` preserves
isomorphisms. The chosen unitors and associator supply the ordinary category
laws. No quotient type or strictness hypothesis is required.

For `CatBicat`, `cat_bicat_homotopy_eq` transparently converts between that
arrow equivalence and `NatIso`. The functors `ToCatCatF` and `FromCatCatF`
act as identities on categories and functors, and
`cat_bicat_homotopy_equiv` supplies chosen quasi-inverses and natural
isomorphisms for their composites. Their comparison requires no equality of
the full category records.

Thus the existing [CatCat.v](../theories/Cat/CatCat.v) has precisely the
intended equality of the general shadow. Its object isomorphisms are
equivalences with chosen quasi-inverses. All noninvertible natural
transformations remain accessible in `CatBicat`.

## An additive example with noninvertible 2-cells

[Instance/Nat/TwoCat.v](../theories/Instance/Nat/TwoCat.v) has one 0-cell, one
1-cell, and natural numbers as 2-cells. Both compositions add natural numbers;
commutativity gives interchange. The theorem `nat_2cell_not_iso` shows that
positive 2-cells are not invertible, so the example does not restrict its
hom-category to a groupoid.

`NatCell1Eq` is the singleton relation on its 1-cells, and
`nat_cell1_eq_to_cell2` sends every witness to the 2-cell `0`.
`NatBicat_IsStrictTwoCat` proves strictness for this presentation: both
composition laws for comparisons reduce to `0 + 0 = 0`, and the chosen
associators and unitors are also `0`. The structure is enabled explicitly,
like the other model structures.

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
