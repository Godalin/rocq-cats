From Cats Require Import
  Instance.Set.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Foundational Category Interfaces

    Import the set model and the category, functor and transformation
    interfaces. Keep these regressions independent of simplicial models
    and expensive constructions. *)

(** * 基础范畴接口

    导入集合模型及范畴、函子、自然变换接口；这些回归保持独立，
    不依赖单纯集模型或重型构造。 *)

(** Complete categories are explicit record values. Importing a canonical
    model must not supply a default ambient category through class search. *)

(** 完整范畴是显式记录值；导入规范模型不得通过类搜索默认选取环境范畴。 *)

Fail Definition unchosen_ambient_category
  : Cat
  := ltac:(typeclasses eauto).

(** Specified endpoints do not select a natural transformation by instance
    search, even when an identity transformation exists. *)

(** 即使恒等自然变换存在，指定两端函子也不会通过实例搜索自动选择自然变换。 *)

Fail Definition unchosen_identity_transformation (C D : Cat) (F : Fct C D)
  : F ⇒ F
  := ltac:(typeclasses eauto).
