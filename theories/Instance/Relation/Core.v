From Cats.Set.Relation Require Export Family.
From Cats Require Import Cat.Preorder.

(** * The Inclusion Category of Relation Families

    Objects are relations on a fixed indexed carrier. An arrow transforms
    witnesses without changing their endpoints. This is the thin category
    of the inclusion preorder: parallel transformations have specified
    unit-valued equality, while the transformations themselves remain data.
    It is not the category whose objects are carriers and arrows relations. *)

(** * 关系族的包含范畴

    对象是固定索引载体上的关系。箭头转换见证，不改变端点。这是包含预序的
    薄范畴：平行转换具有指定的单位类型相等，但转换本身仍是数据。它不同于
    以载体为对象、以关系为箭头的范畴。 *)

(** Reuse the transparent inclusion preorder and the general thin model. *)

(** 复用透明包含预序及一般薄范畴模型。 *)

Definition RelationFamilyCat@{i a r +}
    {I : Type@{i}} (A : I → Type@{a})
  : Cat
  := @PreorderCat (RelationFamily@{i a r _} A) (@RelationFamilyLe I A)
      (RelationFamilyPreorder A).
