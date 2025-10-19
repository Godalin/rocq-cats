# ~~Rocq Abstract Nonsense~~ :)
# Rocq-Cats

A category theory library for self study.

## Key Features

### Category Theory

- Fully Axiom Free / Constructive.

- Modularity with sub-/super- type classes [see here](/theories/Cat/Core.v).

- `CCC` and `ETCS` theories ([see here](/theories/Cat/CCC.v) and [here](/theories/Cat/CCC.v)) can be build up from this modularity.

- A Fully formalized category of sets `SetCat` [see here](/theories/ETCS/Core.v)
  - with the following the Rocq features
    - setoid as sets
    - proper function preserving equivalence relations
    - canonical structure
  
- (Weak version of) Yoneda Lemma can be proved with this target category `SetCat` [see here](/theories/Cat/Natural.v).
  - Weak because functoriality / naturality property about related constructions, only the isomorphism(s).

### ETCS

This project aims at building ETCS.

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
