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
- `theories/Cat/Core.v`: categories, morphism equivalence, duality, products,
  terminal/initial objects, and exponentials.
- Other `theories/Cat/` modules: functors, natural transformations, pullbacks,
  morphism properties, and CCC structure.
- `theories/Instance/Set/Core.v`: setoids, respectful functions, and `SetCat`.
- `theories/Instance/Set/Terminal.v` and `Initial.v`: unit and empty setoids
  with their chosen terminal and initial structures.
- `theories/Instance/Set/Product.v`: setoid products and constructive chosen
  products for `SetCat`.
- `theories/Instance/Set/Exponential.v` and `CCC.v`: respectful-map
  exponentials and the assembled cartesian closed setoid category.
- `theories/Instance/Set/Pullback.v`: constructive chosen pullbacks for `SetCat`.
- `theories/Instance/Set/Fam.v`: dependent functions, coherent families,
  dependent sums, fibers, and their total-space isomorphisms.
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
- Treat equality and coherence as mathematical design decisions. Functor
  comparison must account for morphism action and dependent transports.
  Pointwise equality of natural-transformation components does not require
  equality of their naturality proofs. Setoid-indexed families need coherent
  transport; arbitrary isomorphisms between fibers are insufficient. Distinguish
  strict substitution equations from laws up to equivalence or isomorphism.
- Follow the local notation, universe-polymorphic style, typeclass conventions,
  and short proof patterns. Do not add `Admitted`, `Admit Obligations`, or axioms
  as completed fixes. Existing holes are audit findings, not proof validation.
- Prefer the existing UTF-8 notation (`λ`, `∀`, `→`, `∃`, `∧`, `≈`, `∘`) and
  exported dependent-pair/projection notation over ASCII spellings and explicit
  constructors where unambiguous. Preserve Rocq's required tactic syntax.

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
  `FunEq_Equivalence`; chosen model structures use names such as
  `SetCat_HasPullback`. The name alone does not register a typeclass instance.
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
