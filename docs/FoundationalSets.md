# Sets and designated extensional equality

The migration in [issue #19](https://github.com/Godalin/rocq-cats/issues/19)
uses one mathematical notion of a set: a carrier equipped with a specified,
Type-valued equivalence relation. Rocq's native `eq` is one concrete choice,
as for natural numbers. Function sets use pointwise equality. Equality of
functions, proof irrelevance, UIP, choice and resizing axioms are not required.

## Modules and dependencies

```text
Meta → Set.Core → Set.Morphism → Cat.Core → Instance.Set.Core
```

| Module | Responsibility |
| --- | --- |
| [Set/Core.v](../theories/Set/Core.v) | `SetC`, carrier, designated equality, equivalence laws, `≈S` and `[≈S]` |
| [Set/Morphism.v](../theories/Set/Morphism.v) | Respectful maps, pointwise equality, function sets, identities, composition and their laws |
| [Cat/Core.v](../theories/Cat/Core.v) | Categories with native hom-sets, hom composition and its respectful maps |
| [Instance/Set/Core.v](../theories/Instance/Set/Core.v) | The concrete category `SetCat` |

Neither foundational set module imports categories. `Cat.Core` exports the
set API. `Instance.Set.Core` depends only on `Cat.Core`, and clients import
model extensions individually.

To use sets independently of categories, write:

```coq
From Cats.Set Require Import Core.
From Cats.Set Require Import Morphism.
```

The prefix form avoids using the vernacular keyword `Set` as the first
component after `Require Import`. Set equality notation belongs to
`set_scope` (`%set`); category notation retains its existing scopes.

## The category interface

The primitive field is `HomSet : Ob → Ob → SetC`. `Hom` and `HomEq` are
computed record fields: they extract the carrier and equality of that set.
They add no constructor arguments and make no additional choices. This keeps
the existing named coercion targets used by bundled arrows and preserves
`@Hom`, `@HomEq[X,Y]`, `≈`, `id` and `∘`.

Composition remains a dependent binary operation with `Proper`, so universal
properties and their `is_*`/`Has*` separation keep the same mathematical shape.
`HomEq_Equivalence` is derived from `carrier_setoid`; category constructors no
longer supply a separate equivalence-law field.

| Previous API | Current API |
| --- | --- |
| `Instance.Set.Core.SetC` and carrier projections | `Set.Core.SetC` and its projections |
| Respectful/function-set API in `Instance.Set.Core` | The same names in `Set.Morphism` |
| Separate `Hom` and `HomEq` choices | One `HomSet` choice |
| Reconstructed `Hom_SetC` | Transparent alias of `HomSet`, in `Cat.Core` |
| `comp_l_resp`, `comp_r_resp` in `Instance.Set.Core` | The same general constructions in `Cat.Core` |

The migrated constructions include opposites, products, slices, functor
categories, categories up to natural isomorphism, bicategory homotopy
categories, thin bicategories, and the set/family models. Hom functors now
return `HomSet` directly. Yoneda and the coherent family–slice comparison
retain their original equalities and universal properties.

For some opposite-category proofs, elaboration needs the original category
or arrow endpoints explicitly. Those annotations disambiguate the same
underlying arrows; they do not introduce new equality assumptions.

## Universe constraints

`SetC@{u p}` has type `Type@{max(u+1,p+1)}` with no required inequality
between `u` and `p`. The extraction preserves this signature.

On Rocq 9.0.1 the category signature is still `Cat@{o h p l q}`, with
`h <= q`, `p <= q`, `q <= l` and their redundant consequences. In particular,
`HomSet X Y : SetC@{h p}` imposes neither `h <= p` nor `p <= h`.
The carrier, equality and category universes match the previous interface.

`SetCat@{u p +}` explicitly names the carrier and equality sizes of its
objects first. Its inferred auxiliary parameters follow those two names;
positional applications in fixed-size models were updated accordingly.
The size of a respectful-map carrier includes its respectfulness witnesses,
so the sizes of the resulting category's homs need not be the input `u` and `p`.

The local `p <= u` bound of the fixed-size family–slice equivalence remains:
its fiber representation stores equality witnesses in the carrier. It is
not a constraint on basic sets, general categories or bicategories.

## Future dependent-type interfaces

The intended common vocabulary is `Ty Γ : SetC` and `Tm Γ A : SetC`.
A temporary interface check also uses `Tm Γ : FamS (Ty Γ)`, giving coherent
conversion along designated type equalities and witness-independent actions.
It checks distinct type-carrier, type-equality, term-carrier and term-equality
levels in both directions, without implementing a full CwF.

Choosing arbitrary type isomorphisms as type equality is not automatic:
nontrivial automorphisms may act differently on terms. A model must specify
the equality and its transport policy. Substitution laws and any comparison
isomorphisms remain separate mathematical obligations in
[issue #13](https://github.com/Godalin/rocq-cats/issues/13).

## Validation

[Universes.v](../tests/Universes.v) retains both carrier/equality orderings
for basic sets, `SetCat`, hom-sets, functor categories and thin bicategories;
it checks distinct bicategory cell levels in both 2-cell/equality orderings,
and the fixed-size family–slice equivalence with `p < u`.

Temporary checks verify that importing `Set.Morphism` does not load `Cat`,
retain distinct Boolean equality witnesses, and check computational maps.
They also check the CwF-oriented interface above and inspect inferred
signatures and foundational `Print Assumptions` output. They are not extra
permanent model or test modules.

Locally, `dune build @all @runtest @install` passes with Rocq 9.0.1,
OCaml 5.3.0 and Dune 3.21.0. The foundational checks introduce no additional
axioms. The supported-version CI matrix still needs to run on the migration;
local validation does not establish that matrix's result.
