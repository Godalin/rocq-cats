From Cats.Set Require Export Core.

(** * Pointed Sets

    A pointed set chooses one element of a setoid. Its underlying setoid
    supplies both the carrier and the specified equality. *)

(** * 带点集合

    带点集合从广集中选取一个元素。底层广集同时提供载体和指定相等。 *)

Minks.Mixin HasPoint (S : SetC)
  :=
  { point : S }.

Arguments point {_ _}.

(** Pack a setoid together with its selected point. *)

(** 将广集和它选定的点打包。 *)

Minks.Struct PointedSetC
  extends SetC
  with  hasPoint as hasPoint : HasPoint.
