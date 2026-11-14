From Cats Require Import
  Cat.Diagram.Cocycle.

(** * Independent Coefficient and Hom Equality Sizes

    Exchange the size profiles of the categories, and test coefficients
    with equality strictly below and strictly above their carrier. *)

(** * 独立的系数相等与 Hom 相等大小

    交换范畴的大小配置，并分别测试系数相等严格低于及严格高于载体的情形。 *)

Section Sizes.
Universes e h o l.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Context (I : Cat@{o h e l l}) (J : Cat@{e h o l l})
    (F : Functor I J) (G : Functor J I)
    (M : SetC@{h e}) (N : SetC@{e h})
    `{HM : !Monoid M} `{HN : !Monoid N}
    (c : TwoCocycle J M) (d : TwoCocycle I N).

(** Pullback accepts coefficient equality below its carrier. *)

(** 拉回允许系数相等低于载体。 *)

Definition low_equality_pullback
  : TwoCocycle I M
  := TwoCocyclePullback F c.

(** Exchange source and target; coefficient equality is now higher. *)

(** 交换源与目标，此时系数相等高于载体。 *)

Definition high_equality_pullback
  : TwoCocycle J N
  := TwoCocyclePullback G d.

(** The respectful map also retains these independent levels. *)

(** 保相等映射也保留这些独立层级。 *)

Definition low_equality_map
  : @TwoCocycleS J M HM →r @TwoCocycleS I M HM
  := two_cocycle_pullback_resp F.

(** Composition compares labels in the lower coefficient equality. *)

(** 复合律在较低的系数相等中比较标签。 *)

Definition low_equality_composition
  : TwoCocycleEq (TwoCocyclePullback (F ∘F G) c)
      (TwoCocyclePullback G (TwoCocyclePullback F c))
  := two_cocycle_pullback_comp G F c.

(** Identity comparison also works with higher coefficient equality. *)

(** 恒等比较也适用于较高的系数相等。 *)

Definition high_equality_identity
  : TwoCocycleEq (TwoCocyclePullback IdF d) d
  := two_cocycle_pullback_id d.

End Sizes.
