From Cats.Instance.Relation Require Export Core.
From Cats.Set.Relation Require Export Sum.
From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Coproduct.Core
  Cat.Functor.Core.

(** * Coproducts of Relation Families

    The least-upper-bound property of tagged sums supplies the coproduct
    in the thin inclusion category. Uniqueness uses its specified hom
    equality; it does not equate witness-transforming functions. *)

(** * 关系族的余积

    带标签和的最小上界性质给出薄包含范畴中的余积。唯一性使用该范畴指定的
    Hom 相等，不把转换见证的函数判为相等。 *)

Local Open Scope relation_scope.
Local Open Scope cat_scope.

(** Select the original opposite product structure, with explicit enabling
    by clients rather than a globally registered model choice. *)

(** 选择原有反范畴积结构，由客户端显式启用，不全局注册模型选择。 *)

Program Definition RelationFamilyCat_HasCoproduct@{i a r +}
    {I : Type@{i}} (A : I → Type@{a})
  : HasCoproduct (RelationFamilyCat@{i a r _ _ _} A)
  :=
  {|hasOpProduct :=
      {|Prod := FamilyRelationSum
      ; π1 R S := family_relation_sum_inl R S
      ; π2 R S := family_relation_sum_inr R S
      |}
  |}.
Next Obligation.
  intros T h k. exists (family_relation_sum_case h k).
  refine {|this := (tt, tt)
         ; that := λ g p, tt
         |}.
Defined.

(** The sum is a binary functor on the inclusion category. Its arrow map
    retains the branch and applies the corresponding witness transformer. *)

(** 和是包含范畴上的二元函子，其箭头映射保留分支，并应用对应的见证转换。 *)

Program Definition RelationSumF@{i a r +}
    {I : Type@{i}} (A : I → Type@{a})
  : Functor
      (RelationFamilyCat@{i a r _ _ _} A ×C
        RelationFamilyCat@{i a r _ _ _} A)
      (RelationFamilyCat@{i a r _ _ _} A)
  :=
  {|F0 p := fst p ⊕ᵢ snd p
  ; F1 R S h := family_relation_sum_map (fst h) (snd h)
  |}.
Next Obligation. repeat intro; exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.
