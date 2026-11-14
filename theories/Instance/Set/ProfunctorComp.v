From Cats Require Import
  Cat.Core
  Cat.Profunctor.Compose
  Instance.Set.Core
  Instance.Set.Coend.

(** * Explicit Setoid Profunctor Composites

    Select only the indicated kernel coends. Sufficient middle-category
    bounds are [o,h ≤ u ≤ p], with its Hom-equality level independent.
    Source and target categories need not be smaller than the value bounds.
    No Hom weight is stored in this kernel, and no resizing or fixed-size
    full-setoid self-indexing principle is used. *)

(** * 显式广集 Profunctor 复合

    只选择所指核的 coend。中间范畴的充分大小界为 [o,h ≤ u ≤ p]，其 Hom 相等
    层级保持独立。来源和目标范畴不必小于值界。本核不存储 Hom 权重，不使用
    大小重设或固定大小全广集自索引原则。 *)

(** Enable this specific composite family explicitly; importing the module
    does not register a chosen model instance. *)

(** 显式启用这一特定复合族；导入本模块不注册选定模型实例。 *)

Program Definition SetCat_ProfunctorComp@{o h e u p +}
    {C E : Cat} (D : Cat@{o h e _ _})
    (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _}))
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
  : HasProfunctorComp C D E Q P
  :=
  {|hasProfunctorCompCoend X Z :=
      SetCat_Coend D (ProfunctorCompKernel Q P X Z)
  |}.
