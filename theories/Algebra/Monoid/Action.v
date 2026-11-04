From Cats Require Export
  Algebra.Monoid.Category.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Instance.Set.Core
  Instance.Set.Hom.

Local Open Scope monoid_scope.

(** * The Left Regular Action

    An action is a set-valued functor on the single-object category. The
    regular action is the existing covariant hom functor [Hom(tt,-)]; its
    unit and composition laws are inherited rather than proved again. *)

(** * 左正则作用

    作用是单对象范畴上的集合值函子。正则作用直接使用已有的协变 Hom 函子
    [Hom(tt,-)]，继承其单位律与复合律，不再重复证明。 *)

Definition RegularActionF (M : SetC) `{HM : !Monoid M}
  : Functor B(M) SetCat
  := @ℎ1F B(M) tt.

(** The action of an element is left multiplication. *)

(** 元素的作用就是左乘。 *)

Lemma regular_action_mul {M : SetC} `{HM : !Monoid M} (x y : M)
  : fmap (RegularActionF M) (X := tt) (Y := tt) x y ≈S x ⋅ y.
Proof. reflexivity. Qed.

(** The regular action is faithful: evaluation at the unit recovers an
    element up to its specified equality. *)

(** 正则作用是忠实的：在单位元处求值即在指定相等下恢复原元素。 *)

Definition regular_action_faithful (M : SetC) `{HM : !Monoid M}
  : is_faithful (RegularActionF M).
Proof.
  intros [] [] x y H. specialize (H 1).
  change (x ⋅ 1 ≈S y ⋅ 1) in H.
  rewrite !monoid_unit_r in H. exact H.
Defined.
