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
  
- (Weak version of) Yoneda Lemma can be proved with this target category `SetCat` [see here](/theories/Cat/Natural.v).
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
- [ETCS](./theories/ETCS/): abstract ETCS interfaces and results.

Import the setoid structures that are needed and enable chosen structures explicitly:

```coq
From Cats Require Import Instance.Set.Core.
From Cats Require Import Instance.Set.Product Instance.Set.Pullback.

Local Existing Instance SetCat_HasProduct.
Local Existing Instance SetCat_HasPullback.
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
