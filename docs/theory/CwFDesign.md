# Categories with families

A family-valued presheaf `T : Fct (C^op) FamCat` supplies the types at each
context, terms in each type, and substitution along context maps. Types and
terms have specified setoid equalities. A witness of type equality transports
terms, coherently with identity, composition and substitution. An arbitrary
fiber isomorphism does not establish that specified equality.
[Families and slices](FamiliesAndSlices.md) · [CwF core](../../theories/DTT/CwF.v)

## Interface components

`HasContextExtension`, `HasDisplay` and `HasContextRepresentation` are
Minks mixins over their specified presheaves. Their existing operations,
Type-valued universal witnesses and laws are defined once. None selects a
model merely by import.

`CwF C` is a Minks structure with the family-valued presheaf as its primary
underlying view. `MakeCwF C T HT HC` stores exactly that functor, its
`HasContextExtension T` witness and an independently supplied
`HasTerminal C`. Generated projections provide the two stored choices;
ordinary coercion supplies `T` when a functor is expected. The complete
object is not a class to be searched for, and the former `TyTmF` record
field is replaced by that underlying view. Fixed-presheaf theorems continue
to require only their relevant mixins.

[Hierarchy development](../development/HierarchyDevelopment.md) ·
[Minks interface regressions](../../tests/dtt/MinksInterfaces.v)

## Extending a context

For a context Γ and a type A over it, choose an extension, its projection to Γ,
and its generic term. A substitution into Γ paired with a term of the
substituted type determines a map into the extension. The projection and
term equations characterize that map up to hom equality. This separates
the universal property of a candidate from the choice of extensions.
[Extension](../../theories/DTT/Context/Extension.v) · [Conversion](../../theories/DTT/Context/Conversion.v)

Lifting substitutions along display projections gives pullback squares.
Terms correspond to sections of the chosen projections. Comprehension
packages those display maps and their behavior under substitution.
[Pullbacks](../../theories/DTT/Context/Pullback.v) · [Sections](../../theories/DTT/Context/Section.v) · [Comprehension](../../theories/DTT/Comprehension.v)

## Models and size

The setoid model starts with a setoid of type codes and a coherent family
of elements over those codes. Context extension pairs an environment with
an element of its interpreted type. The CwF core can be used independently
of particular type constructors. The universes for context maps, type codes,
terms and their equality witnesses are tracked separately.
[Code/El model](../../theories/Instance/Set/CwF.v) · [Recovery criteria](CwFRecovery.md) · [Universe checks](../../tests/Universes.v)

For a coherent family El over Code, the data in context Γ take the following form:

```text
Ty Γ         = respectful maps Γ → Code
Tm Γ A       = sections of the family El reindexed along A
A[σ]         = A ∘ σ
Γ.A          = dependent pairs (γ, a) with a in El(A γ)
p(γ, a)      = γ
q(γ, a)      = a
⟨σ, t⟩(δ)    = (σ δ, t δ)
```

The empty context is the selected terminal object. Over an arbitrary base
category the same projection, generic term and pairing equations express
extension without reference to elements of a set.
