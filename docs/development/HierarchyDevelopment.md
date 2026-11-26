# Developing mathematical interfaces

Use Minks as the sole declaration language for new and migrated Cats mathematical
structures. Declare increments with `Minks.Mixin` and complete bundles with
`Minks.Struct`. Rocq classes and records are the generated interfaces seen by
clients. Construct values and prove laws with ordinary Rocq commands.

## Components and shared choices

- State the theorem for the components used by its statement and proof. In
  `TensorUnitorLIsoN`, tensor actions, interchange and unitors suffice.
  `tensor_map_triangle` also needs the associator and its triangle law.
  Extract a reusable intermediate layer when a client uses it. Prove
  derivable respectfulness from the defining laws and expose the resulting
  `Proper` instance where useful. [Monoidal.v](../../theories/Cat/Monoidal/Monoidal.v)
- Use `Minks.Mixin` for an increment over specified data. `Is*` expresses
  laws of given operations and `Has*` selects data over a fixed base. Keep
  computational witnesses in `Type`. Use `Minks.Struct` for a first-class
  bundle, possibly with ordinary parameters such as source and target.
  Use `extends` for parents and `with key : Mixin` for a new component.
  Define each operation once at the layer that introduces it. [Applicative](../../theories/Cat/Applicative/Core.v)
- Share a choice by inheriting the same component key with the same
  dependencies. In `MonoidalCat` the pentagon and triangle refer to the
  same tensor and associator. A merge can consist entirely of parents.
  Use a relative export such as `exports HasMonoidal [carrier]` when clients
  need the combined structure on a fixed base. It provides a class for
  clients and represents the component combination for later declarations. [MonoidalCat](../../theories/Cat/Monoidal/Monoidal.v) · [Minks command rules](../../minks/README.md)
- Use the generated constructor, direct-parent packers and ancestor views.
  Use `Minks.Inspect` to check component keys, sharing and available views.
  Derive multiple views from shared components. Add a manual conversion only for a
  meaningful path missing from the constructor and projection chains. Use
  `SourceToTarget` for a parent view and `TargetOfParent` for packing.

## Parameters and instance search

Choose the public call first. With `C D : MonoidalCat`, this is a complete
client. Coercions supply the underlying categories and instance search
supplies their selected monoidal structures.

```coq
From Cats Require Import
  Cat.Monoidal.Transport.

Section PackedUse.
Context (C D : MonoidalCat) (L : LaxMonoidalFct C D).
Check LaxMonoidF L : Fct (MonoidCat C) (MonoidCat D).
End PackedUse.
```

- **Binders.** Keep the mathematical input explicit when it identifies
  the construction (`MonoidCat C`, `LaxMonoidalFct C D`). Use `{X : C}` for
  an endpoint inferred from arrows, and a named generalized binder such as
  `` `{MC : !HasMonoidal C} `` for a choice to be found by instance search.
  Here `!` asks Rocq to take the supplied class application as written;
  the braces control implicitness. A backtick with parentheses gives a
  class parameter passed positionally.
  An ordinary class-valued parameter can represent a particular witness
  supplied by the caller. A class binder in Minks is an ordinary parameter
  unless a component dependency is declared. Keep this distinction in public
  notation too: `st[X; Y]` takes the objects and lets Rocq infer the chosen
  strength. [Tensorial strength](../../theories/Cat/Monoidal/Strength.v)
- **Sections.** Share hypotheses used throughout related constructions
  with `Context`. Introduce extra assumptions where they first become
  necessary. Give a public construction its explicit base in its header
  when that makes subsequent types read naturally. Check the generalized
  signature after `End` with `Print Implicit` and an actual application. [Monoid.v](../../theories/Cat/Monoidal/Monoid.v)
- **Views and registrations.** Use the coercion for a unique underlying
  object, function or functor (`Hom A B`, `F X`, `fmap F f`). A coercion supplies an underlying view when a term has an expected type.
  Instance search supplies a class witness when elaborating an operation.
  Use Canonical Structures for inference from known projections. Reuse
  registrations provided by Minks. Keep packers that require missing
  components explicit; a reverse Canonical that searches for them can
  re-enter the same instance search. Register a model choice globally only
  when it is a designated default, as with the standard terminal object
  and binary products in their respective `SetCat` modules.
- **Multiple choices.** Keep each operation tied to the witness that
  selected it. For two structures on `C`, write
  `F : @LaxMonoidalFct C C source target`. For Day convolution, write
  `@MonoidCat _ DM` to select the tensor determined by the supplied Day
  data. In bundle notation such as `m[A]`, bind the stored evidence in the
  interpretation so the caller only supplies `A`. [TwoUnits and MonoidChoices](../../tests/category/MonoidalExports.v)
- **Inference in proofs.** Try the public law directly (`exact fmap_proper`,
  `rewrite fmap_comp`). If inference stalls, give the smallest informative
  argument, e.g. `(obj := F)`, `(A : Ob _)`, or a selected instance. Use
  `@` when positional control is clearer. An explicit argument is worth
  keeping if omitting it causes expensive search. For `Proper`, keep fixed
  context inputs before the varying arrow so the partial application rewrites
  (e.g. `arrow_context A Z f`). Apply existing laws and projections directly;
  a forwarding `Let` makes it harder to see which choice a proof uses. [Bifct](../../theories/Cat/Monoidal/Bifct.v) · [Day monoids](../../theories/Cat/Day/Monoid.v)

## Proofs, modules and checks

- Express an equation first at the level where it is easy to prove.
  `SetStrengthN` proves equality of the pairing maps, applies `fmap_proper`
  once, then rewrites `fmap_comp`. Prefer public comparison laws such as
  `cartesian_tensor_map` when a derived tensor computes only up to `HomEq`.
  Keep maps and selected inverses transparent for projection and computation. [Set strength](../../theories/Instance/Set/Strength.v) · [Proof transparency](CodeStyle.md#proof-transparency)
- Keep a construction, its naturality and the laws used by its clients
  together when they use the same imports and assumptions. Package a natural
  isomorphism directly when its forward map and chosen inverses are known. A useful general
  result or a concrete model with additional dependencies merits a separate
  module. Merge sections that now share a context; keep weaker results
  available before the stronger assumptions. Update imports and consumers
  in the same migration; remove superseded wrappers. [Cartesian monoidal structure](../../theories/Cat/Monoidal/Cartesian.v)
- Verify the property the change could affect. Check a diamond by conversion,
  a choice by computing a projection, and an ambiguous choice with a
  positive and a negative application. When moving binders between a section
  and a header, inspect the inferred signature with `Set Printing Universes`. For `MonoidCat`, the universe
  of objects may be strictly above or below the bound carried by `HasMonoidal`;
  both applications must elaborate. Use the existing test targets and stop the
  migration when the interfaces and their consumers pass the agreed checks. [Universe regressions](../../tests/Universes.v) · [Development checks](Testing.md)
