From Cats Require Import
  Instance.Set.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Foundational Category Interfaces

    Import the set model and the category, functor and transformation
    interfaces. Keep these regressions independent of simplicial models
    and expensive constructions. *)

(** Complete categories are explicit record values. Importing a canonical
    model must not supply a default ambient category through class search. *)

Fail Definition unchosen_ambient_category
  : Cat
  := ltac:(typeclasses eauto).

(** Specified endpoints do not select a natural transformation by instance
    search, even when an identity transformation exists. *)

Fail Definition unchosen_identity_transformation (C D : Cat) (F : Fct C D)
  : F ⇒ F
  := ltac:(typeclasses eauto).
