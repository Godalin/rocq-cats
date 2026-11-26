# Universes of structured categories

The complete bundles now support two further constructions with the shape
`X : X`. Each occurrence has its own universe instance: a small structured
category is an object of a larger one. These are ordinary universe-polymorphic
families, with no additional axioms or universe self-containment.

```coq
From Cats Require Import
  Cat.Core
  Cat.Cartesian.Core
  Cat.Cartesian.Category
  Cat.Groupoid.Core
  Cat.Groupoid.Category.

Check CartCatCartCat : CartCatCartCat : CartCatCartCat : CartCatCartCat.
Check GpdGpd : GpdGpd : GpdGpd : GpdGpd.
```

These checks appear immediately after the corresponding constructions.
The annotations associate to the right, and each occurrence receives a fresh
universe instance subject to the required size bounds.
The type coercion interprets the right-hand bundle as its object type, so
`CartCatCartCat : CartCatCartCat` elaborates to `CartCatCartCat : @Ob CartCatCartCat`; similarly for
`GpdGpd`. Import the corresponding `Core` modules to bring the coercions
into scope in clients.

## Cartesian categories

[CartCatCat](../../theories/Cat/Cartesian/Category.v) has complete `CartCat`
bundles as objects and finite-product-preserving `CartFct` values as arrows.
Its hom equality is natural isomorphism of the underlying functors, retaining
components and their inverses without comparing preservation records.
`CartFctS C D` uses exactly the terminal and product choices stored in `C`.

`TerminalCart` is the one-point category, and `ProdCart C D` has the
componentwise finite products of its two parents. `TerminalCartF`,
`FstCartF`, `SndCartF` and `PairCartF` provide the terminal arrow, projections
and product mediator. Their universal properties compare functors by natural
isomorphism. `CartCatCartCat : CartCat` packages these choices over `CartCatCat`
through its single inherited category; importing the module registers no
chosen `HasTerminal` or `HasProduct` model on an unrelated category.

The universal-property proofs are reusable before bundling:
[Product.Componentwise](../../theories/Cat/Product/Componentwise.v) combines
terminal and product candidates in arbitrary product categories;
[Functor.Product](../../theories/Cat/Functor/Product.v) combines natural
isomorphisms into a product category. The pointed codiscrete and bundled
product constructions live in
[Cartesian.Construction](../../theories/Cat/Cartesian/Construction.v).

## Groupoids and equivalences

[CoreGpd C](../../theories/Cat/Groupoid/CoreGpd.v) is the core of any category:
objects stay unchanged, and arrows retain precisely the isomorphisms together
with their chosen inverse data. Hom equality is inherited from `C`, so it
does not compare inverse witnesses. `CoreInclusionF` forgets that data and is
faithful. Specify the ambient category explicitly when the original category
and its core share the same object type.

[GpdCat](../../theories/Cat/Groupoid/Category.v) has groupoids as objects and
ordinary functors as arrows, compared by natural isomorphism. Consequently
`GpdGpd := CoreGpd GpdCat` has groupoid equivalences as arrows: each
carries a quasi-inverse and two natural isomorphisms. This reuses the existing
isomorphism theory rather than defining a second equivalence interface.
`GpdForgetF : Fct GpdGpd CatCat` retains the forward functor.

## Checks

[StructureUniverses](../../tests/category/StructureUniverses.v) checks ordinary product
laws and rewriting, computation with distinct
terminal/product choices on the same category, a nontrivial groupoid
self-equivalence and its selected inverse, and both strict orders of hom and
equality sizes. Products also accept parents with different size profiles.
