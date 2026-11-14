From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Day.Core
  Instance.Set.Core
  Instance.Set.Coend.

(** * Explicit Setoid Day Convolutions *)

(** * 显式的广集 Day 卷积 *)

(** Select just the coends of the Day kernels. Sufficient size bounds are
    [o,h ≤ u ≤ p] and [e ≤ p], where [o,h,e] are the base category's object,
    hom-carrier and hom-equality levels, and [u,p] are the target setoid
    carrier and equality levels. The Hom weight accounts for [e ≤ p],
    unlike a general coend whose kernel does not retain that hom-setoid.
    Carrier and equality levels are raised independently, never resized.
    No strength is needed here; monoidal coherence is a later structure.
    Importing this module does not select a model globally. *)

(** 仅为 Day 核选择 coend。充分大小界为 [o,h ≤ u ≤ p] 及 [e ≤ p]，其中
    [o,h,e] 是基范畴的对象、Hom 载体和 Hom 相等层级，[u,p] 是目标广集的
    载体与相等层级。Hom 权重导致 [e ≤ p]，有别于不保存该 Hom 广集的一般
    coend 核。载体与相等层级独立提升，不重设大小。这里不需要强度；幺半
    相干性是后续结构。导入此模块不全局选择模型。 *)

Program Definition SetCat_Day@{o h e u p +} (C : Cat@{o h e _ _})
    (T : Functor (C ×C C) C)
    (F G : Functor C (SetCat@{u p _ _ _ _ _}))
  : HasDay C T F G
  :=
  {|hasDayCoend Z := SetCat_Coend (C ×C C) (DayKernel T F G Z)
  |}.
