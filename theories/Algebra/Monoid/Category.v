From Cats Require Export
  Algebra.Monoid.Core.
From Cats Require Import
  Cat.Core.

Local Open Scope monoid_scope.

(** * Monoids and Single-Object Categories

    Multiplication [g ⋅ f] is categorical composition [g ∘ f]. The sole
    object is literally [unit], so no equality between arbitrary isomorphic
    objects is needed. Equality of arrows is the original setoid equality. *)

(** * 幺半群与单对象范畴

    乘法 [g ⋅ f] 解释为范畴复合 [g ∘ f]。对象类型确为 [unit]，无需等同任意
    同构对象；箭头相等直接使用原广集的相等。 *)

Program Definition MonoidCat (M : SetC) `{HM : !Monoid M}
  : Cat
  :=
  {|Ob := unit
  ; HomSet _ _ := M
  ; id _ := 1
  ; comp _ _ _ g f := g ⋅ f
  ; comp_proper _ _ _ := monoid_mul_proper
  ; comp_id_r _ _ := monoid_unit_r
  ; comp_id_l _ _ := monoid_unit_l
  ; comp_assoc _ _ _ _ := monoid_assoc
  |}.

Notation "'B(' M ')'" := (MonoidCat M) : cat_scope.

(** Endomorphisms of any specified object form a monoid. This provides the
    reverse construction in particular for a specified singleton category. *)

(** 任意指定对象的自态射构成幺半群；特别地，这给出指定单对象范畴的反向构造。 *)

Program Definition EndMonoid (C : Cat) (X : @Ob C)
  : Monoid (HomSet X X)
  :=
  {|monoid_unit := @id X
  ; monoid_mul g f := g ∘ f
  ; monoid_mul_proper := comp_proper
  ; monoid_unit_l := comp_id_l
  ; monoid_unit_r := comp_id_r
  ; monoid_assoc := comp_assoc
  |}.
