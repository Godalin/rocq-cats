# Working on Rocq-Cats

## Purpose and scope

This is a personal learning and experimentation library for constructive category
theory in Rocq. Follow the design principles in
[issue #1](https://github.com/Godalin/rocq-cats/issues/1). Develop small, reusable
categorical components and assemble semantic models from them. CCC/STLC, ETCS,
and CwF/dependent type theory are independent directions; none is the mandatory
foundation of the whole library. Prefer readable mathematics and incremental
changes over framework machinery or repository-wide rewrites.

## Repository map

- `theories/Meta.v`: Type-valued logic, equivalence relations, uniqueness, and
  shared proof helpers.
- `theories/Cat/Core.v`: categories, morphism equivalence, object-equality
  transports, duality, product categories, and isomorphisms.
- `theories/Cat/Terminal.v`: terminal objects and their dual initial objects.
- `theories/Cat/Product.v`: binary products, pairing, product morphisms, and
  their interaction with terminal objects.
- `theories/Cat/Exponential.v`: exponential objects, evaluation, and currying.
- `theories/Cat/Fibration.v`: cartesian morphisms, universal factorization,
  comparison of lifts over a base isomorphism, and chosen cartesian lifts.
- `theories/Cat/Comprehension.v`: chosen lifts, total-space functors, natural
  display projections, and the property that cartesian morphisms give pullbacks.
- `theories/Cat/Functor.v`: functors, composition, fixing arguments, and opposites.
- `theories/Cat/Natural.v`: natural transformations, natural isomorphisms as
  functor equivalence, whiskering, and preservation of these comparisons.
- `theories/Cat/CatCat.v`: categories with functors as arrows and natural
  isomorphism as arrow equivalence; category equivalence and opposite categories.
- `theories/Cat/Bicategory.v`: hom-categories, horizontal composition,
  interchange, and coherent associators/unitors.
- `theories/Cat/TwoCategory.v`: strictness relative to an explicit 1-cell
  equivalence, with coherent comparison 2-cells and strict coherence maps.
- `theories/Cat/CatBicat.v`: categories, functors, and all natural transformations
  as a bicategory presentation, with pentagon and triangle coherence.
- `theories/Instance/Nat/TwoCat.v`: an additive bicategory with one object, one
  1-cell, and additive natural-number 2-cells, including noninvertible ones;
  its strictness uses the singleton 1-cell setoid.
- Other `theories/Cat/` modules: pullbacks, morphism properties, and CCC structure.
- `theories/Instance/Set/Core.v`: setoids, respectful functions, and `SetCat`.
- `theories/Instance/Set/Terminal.v` and `Initial.v`: unit and empty setoids
  with their chosen terminal and initial structures.
- `theories/Instance/Set/Product.v`: setoid products and constructive chosen
  products for `SetCat`.
- `theories/Instance/Set/Exponential.v` and `CCC.v`: respectful-map
  exponentials and the assembled cartesian closed setoid category.
- `theories/Instance/Set/Nat.v`: the discrete natural-number setoid and its
  natural-numbers-object structure with computational recursion.
- `theories/Instance/Set/Pullback.v`: constructive chosen pullbacks for `SetCat`.
- `theories/Instance/Set/Fam.v`: dependent functions, coherent families,
  reindexing, dependent sums, fibers, and their total-space isomorphisms.
- `theories/Instance/Set/FamCat.v`: the category of coherent families, with
  transport-compatible morphisms and transport-aware morphism equivalence;
  base and total-space functors, with projection as a natural transformation.
- `theories/Instance/Set/FamReindex.v`: canonical reindexing morphisms and
  the pullback universal property of their total-space squares; explicit
  identity and composition comparison isomorphisms.
- `theories/Instance/Set/FamFibration.v`: cartesian reindexing for the family
  base functor, explicitly enabled chosen lifts, and reindexed family morphisms.
- `theories/Instance/Set/FamComprehension.v`: the comprehension structure of
  coherent families, its pullback property for every cartesian family morphism,
  and the identification of family terms with sections of display projections.
- `theories/Instance/Set/FamSection.v`: coherent dependent sections and their
  pointwise setoid, section reindexing, the generic element, and total-space
  pairing with its universal property and computation laws; the setoid of
  projection sections and its isomorphism with coherent sections.
- `theories/Instance/Set/FamSectionMap.v`: family morphisms acting on sections,
  including reindexed sections, transport-aware equivalence, and compatibility
  with identity, composition, reindexing, and total-space pairing; the connection
  between reindexed family morphisms and their action on sections.
- `theories/Instance/Set/Hom.v`, `Yoneda.v`, `Presheaf.v`, and `Subobject.v`:
  set-valued Hom-functors, representability, Yoneda, presheaves, and the
  subobject functor.
- `theories/ETCS/`: subobjects, classifiers, natural numbers, and ETCS axioms.
- `dune-project` and `theories/dune`: build configuration; the logical namespace
  is `Cats`. `rocq-cats.opam` is generated: edit `dune-project` instead.

Group concrete implementations under `Instance/<base>/`; keep abstract
interfaces, general constructions, and their typeclass instances with their
theories. `Instance.Set.Core` depends only on `Cat.Core`; it must not import
the setoid extensions, functors, or natural transformations. Import extensions
individually. Chosen structures are explicitly enabled;
their directory location does not register them as global instances.

## Mathematical conventions

- Preserve constructive witness data. The library uses Type-valued relations
  and `sigT` witnesses; do not silently replace them with Prop-only interfaces.
- Use each category's `HomEq` and prove operations respect it (`Proper`). In
  setoid models, use pointwise setoid equivalence where appropriate rather than
  requiring equality of functions.
- Do not introduce functional extensionality, UIP, proof irrelevance, choice,
  classical axioms, or strictification without making the assumption explicit
  and explaining why it is needed. Check generated proof assumptions when
  dependent elimination or automation may introduce them.
- Distinguish `is_*` universal properties of specific candidates from `Has*`
  chosen constructions. General theorems should use the weakest sufficient
  assumptions. Prefer a shared universal-property definition, but evaluate
  proof usability and computation on one interface before broader migration.
  Keep witnesses used to extract mediating maps transparent so that model
  implementations retain their computation rules.
- Treat equality and coherence as mathematical design decisions. Compare
  functors by natural isomorphism, retaining component isomorphisms and
  naturality rather than requiring Rocq equality of their object values.
  Pointwise equality of natural-transformation components does not require
  equality of their naturality proofs. Setoid-indexed families need coherent
  transport; arbitrary isomorphisms between fibers are insufficient. Distinguish
  strict substitution equations from laws up to equivalence or isomorphism.
- Keep levels of higher structure explicit. `CatCat` with `NatIso` as `HomEq`
  is a one-dimensional shadow; the hom-categories in `CatBicat` retain all
  natural transformations. Do not infer strict 1-cell equality from invertible
  2-cells. Specify associators/unitors and their coherence when needed; see
  [the two-dimensional design note](docs/TwoCategories.md).
- Follow the local notation, universe-polymorphic style, typeclass conventions,
  and short proof patterns. Do not add `Admitted`, `Admit Obligations`, or axioms
  as completed fixes. Existing holes are audit findings, not proof validation.
- For category-like interfaces, bundle structural data and laws in one `Class`,
  following `Cat` and `Bicat`. Do not introduce a separate `*Data` record merely
  to stage the declaration; keep derived operations as definitions.
- Construct structures with `Program Definition` (or the established
  `Program Canonical`/`Program Instance` form): state the data in a record
  literal with named fields, then prove the remaining laws in `Next Obligation`.
  Keep computational witnesses transparent with `Defined`, especially inverse
  maps, transport and universal mediators. Complete record literals need no
  obligations. In proofs that extract data in stages, use named record fields
  with `refine` instead; avoid positional `Build_*`/`mkNat` applications unless
  a concrete elaboration limitation requires them.
- The default obligation tactic is `cats_obligation` from `Meta`: introduce
  parameters and simplify the goal and context with `cbn`, without solving
  them. Prove laws explicitly; do not restore the Stdlib's automatic destruction
  of dependent witnesses merely to shorten obligation proofs.
- Prefer the existing UTF-8 notation (`λ`, `∀`, `→`, `∃`, `∧`, `≈`, `∘`) and
  exported dependent-pair/projection notation over ASCII spellings and explicit
  constructors where unambiguous. Preserve Rocq's required tactic syntax.
- Design useful notation alongside new mathematical definitions and operations,
  and use it in related definitions and theorem statements. Follow established
  scope and suffix conventions; check precedence, chaining, and parsing.

## Naming conventions

- Use the nearest established mathematical interface as the naming guide.
  Structures and object-level constructions use capitalized names, such as
  `Cat`, `Functor`, `HasProduct`, `ProdS`, and `IdF`. Keep the `Has*` convention
  for chosen structure and `Is*` for property classes.
- Preserve the mathematical meaning of established abbreviations: `S` means
  Set, implemented here by setoids; `C` means Cat, as in `SetC`, the sets used
  as categorical objects. `SetCat` is their category. Use `F` for functors and
  `N` for natural transformations; lowercase `f` in `≈f` refers to functions.
  In `nt_comp_v` and `∘Nv`, `v` means vertical composition; `op` means opposite.
  Follow nearby names rather than imposing one suffix on every declaration;
  `S` also occurs in operations such as `transpS`, not only in constructions
  such as `ProdS` and `SigS`.
- Ordinary operations and helpers use lowercase words separated by underscores.
  `resp` means respectful (preserving equivalence), also abbreviated by `r` in
  `→r`. Use `_resp` for respectful-map constructions where it follows the local
  API, as in `id_resp`, `comp_resp`, and `comp_l_resp`; this does not require
  renaming every existing set-level map. Distinguish `→r`, a respectful map,
  from `→S`, the set of such maps with pointwise equivalence.
  Use `_proper` for a preservation property or its proof, rather than the
  bundled map. In `_l` and `_r`, the letters mean left and right; `_pre` and
  `_post` mean precomposition and postcomposition.
  Preserve a subject's established spelling when extending its API, as in
  `Sub_fmap`, `NatIso_inv`, and `transpS_inv`.
- Predicates use `is_*`; equivalence relations use the established `*Eq` pattern.
  Equivalence and other typeclass witnesses use `<subject>_<Class>`, following
  `FunEq_Equivalence` and `NatIso_Equivalence`; chosen model structures use names
  such as `SetCat_HasPullback`. The name alone does not register a typeclass
  instance.
- Structure laws and derived results use a mathematical subject prefix and a
  descriptive property, following `comp_assoc`, `functor_comp`, `transpS_id`,
  `product_universal`, `product_pair_unique`, and `yoneda_lemma_iso`.
  Do not distinguish fields from proved lemmas by an `axiom_` prefix; their
  declarations determine their logical role. Use `_universal` for a full
  universal property and specify the mediator when naming its uniqueness,
  as in `product_pair_unique`, to distinguish it from object uniqueness
  up to isomorphism (`product_unique`). Keep related product results under
  `product_`, such as `product_comp_r` and `product_β1`.
  Reuse established endings such as `_id`, `_comp`,
  `_inv`, `_proper`, `_unique`, `_β1`, and `_η` when they express the result.
  Prefer descriptive endings such as `_iso` to a prime on a theorem name.
  Numerical labels follow the local interface: `F0` and `F1` are object and
  morphism actions, while `π1` and `π2` are the two product projections.
- Prefer a precise name over an unexplained abbreviation. Existing names may
  be updated in a focused naming change when their mathematical role becomes
  clearer; update repository references together. Preserve meaningful local
  conventions without turning naming work into a repository-wide API rewrite
  or adding compatibility aliases unless they are needed.

## Working tree and experiments

- Inspect Git status before edits and preserve user work. Uncommitted files may
  be experiments, not the intended baseline for an audit.
- When asked to save experiments, use a named stash including relevant
  untracked files, verify the stash contents, and report how to restore it.
  Keep task deliverables outside that stash. Do not discard or automatically
  reapply experiments over subsequent changes.
- Distinguish findings about the committed baseline from experimental code.
  Report concrete mathematical consequences with file/line references. Do not
  turn an audit request into an unsolicited mass refactor.

## Environment and validation

- Development tools are available through the user's Nix environment. Check
  tool resolution in a properly initialized login shell; do not assume the
  macOS system Git/Xcode toolchain is usable. A sandbox may block shell
  initialization or Nix paths; use the normal approval mechanism when needed.
- Do not change global shell settings or install dependencies merely to work
  around an environment that has not been loaded. Check available Rocq/Coq,
  Stdlib, and Dune versions before diagnosing project failures.
- The project requires Dune >= 3.17 and Rocq/Stdlib >= 9.0. CI covers Rocq 9.0,
  9.1, latest, and dev. Local validation only establishes results for the local
  toolchain.
- Use the existing VS Code build task when applicable; the underlying build is
  `dune build`. For proof changes, compile the affected modules and their
  dependents. Run appropriate broader checks after interface changes.
- For foundational proofs or suspected hidden axioms, inspect
  `Print Assumptions` on the relevant declarations. A successful build alone
  does not establish that a theorem is free of admitted assumptions.
- Keep this theory library lean: prefer general proofs, compilation, and
  targeted assumption checks over tests that merely restate proved laws.
- Keep permanent tests only when they catch a concrete interface regression.
  Put reusable mathematical constructions in theory modules; use temporary
  checks for one-off counterexamples and exploratory instances. Do not leave
  routine `Print Assumptions` output in compiled library or test files.
- Do not edit generated `_build/` files. Avoid cleaning build artifacts unless
  needed to resolve a demonstrated stale-build problem.
- State what was actually checked, the toolchain used, and any remaining
  limitations. Keep validation proportional to the change.
