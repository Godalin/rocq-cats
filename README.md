# ~~Rocq Abstract Nonsense~~ :)
# Rocq-Cats

A category theory library for self study.

## Key Features

### Category Theory

- Fully Axiom Free / Constructive.

- Modularity with sub-/super- type classes [see here](/theories/Cat/Core.v).

- `CCC` and `ETCS` theories ([see here](/theories/Cat/CCC.v) and [here](/theories/Cat/CCC.v)) can be build up from this modularity.

- A Fully formalized category of sets `SetCat` [see here](./theories/Instance/Set/Core.v)
  - with the following the Rocq features
    - setoid as sets
    - proper function preserving equivalence relations
    - canonical structure
  
- (Weak version of) Yoneda Lemma can be proved with this target category `SetCat` [see here](./theories/Instance/Set/Yoneda.v).
  - Weak because functoriality / naturality property about related constructions, only the isomorphism(s).

### ETCS

This project aims at building ETCS.

## Repository layout

- [Cat](./theories/Cat/): categorical interfaces and general constructions.
- [Instance/Set](./theories/Instance/Set/): concrete implementations using setoids
  as sets. [Core](./theories/Instance/Set/Core.v) defines sets, respectful maps,
  and their category; [Product](./theories/Instance/Set/Product.v),
  [Pullback](./theories/Instance/Set/Pullback.v), and
  [Fam](./theories/Instance/Set/Fam.v) provide independent extensions.
  [Hom](./theories/Instance/Set/Hom.v), [Yoneda](./theories/Instance/Set/Yoneda.v),
  [Presheaf](./theories/Instance/Set/Presheaf.v), and
  [Subobject](./theories/Instance/Set/Subobject.v) contain the set-valued
  constructions.
  [Terminal](./theories/Instance/Set/Terminal.v) and
  [Initial](./theories/Instance/Set/Initial.v) provide the unit and empty objects.
  [Exponential](./theories/Instance/Set/Exponential.v) constructs respectful-map
  exponentials; [CCC](./theories/Instance/Set/CCC.v) assembles the cartesian
  closed structure without additional axioms.
  [Nat](./theories/Instance/Set/Nat.v) provides a natural-numbers object with
  computational recursion.
- [ETCS](./theories/ETCS/): abstract ETCS interfaces and results.

Import the setoid structures that are needed and enable chosen structures explicitly:

```coq
From Cats Require Import Instance.Set.Core.
From Cats Require Import Instance.Set.Product Instance.Set.Pullback.

Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasPullback.
```

The complete cartesian closed structure can also be enabled as a bundle:

```coq
From Cats Require Import Instance.Set.CCC.
Local Existing Instance SetCat_CCC.
```

## TODOs

- [x] Pullbacks
- [ ] Limits
- [ ] Adjoint Functor
- [ ] Univalence Category
- [ ] Enriched Category
- [ ] ETCS constructions
  - [x] Sub-object
  - [ ] Relations
  - [ ] Numbers
  - [ ] Well Orderings
  - [ ] AC
  - [ ] Cardinal Arithmetics
- [ ] *TBA*
