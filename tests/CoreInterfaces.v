From Cats Require Import
  Instance.Set.Core.

(** * Foundational Category Interfaces

    Import only the set model and its category foundation. This regression
    must stay independent of simplicial models and expensive constructions. *)

(** * 基础范畴接口

    只导入集合模型及其范畴基础；此回归保持独立，不依赖单纯集模型或重型构造。 *)

(** Complete categories are explicit record values. Importing a canonical
    model must not supply a default ambient category through class search. *)

(** 完整范畴是显式记录值；导入规范模型不得通过类搜索默认选取环境范畴。 *)

Fail Definition unchosen_ambient_category
  : Cat
  := ltac:(typeclasses eauto).
