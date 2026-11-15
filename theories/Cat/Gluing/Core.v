From Cats Require Export Cat.Comma.Core.

(** * Gluing along a Functor

    For [F : C → D], an object consists of [X] in [D], [A] in [C], and
    an arrow [X → F A]. A map is a commuting square. Reuse the existing
    comma category; equality compares side maps and retains square
    witnesses without identifying them. This module makes no limit or
    cartesian-closure assumption. *)

(** * 沿函子的粘合

    对 [F : C → D]，对象由 [D] 中的 [X]、[C] 中的 [A] 及箭头
    [X → F A] 组成，映射为交换方形。复用已有逗号范畴；相等比较两条侧边，
    保留方形见证而不识别它们。本模块不假设极限或笛卡尔闭结构。 *)

(** The original comma category is the only underlying construction. *)

(** 原逗号范畴是唯一的底层构造。 *)

Definition Gluing {C D : Cat} (F : Fct C D)
  : Cat
  := IdF ↓C F.

(** Forget the base object and retain the domain in [D]. *)

(** 忘却基对象，保留 [D] 中的定义域。 *)

Definition GluingLeftF {C D : Cat} (F : Fct C D)
  : Fct (Gluing F) D
  := CommaLeftF IdF F.

(** Retain the base object in [C]. *)

(** 保留 [C] 中的基对象。 *)

Definition GluingRightF {C D : Cat} (F : Fct C D)
  : Fct (Gluing F) C
  := CommaRightF IdF F.

(** The stored arrows give the natural comparison between projections. *)

(** 存储的箭头给出两个投影之间的自然比较。 *)

Program Definition GluingArrowN {C D : Cat} (F : Fct C D)
  : GluingLeftF F ⇒ F ∘F GluingRightF F
  :=
  {|nt X := comma_arrow X
  |}.
Next Obligation. symmetry. exact (comma_comm f). Defined.
