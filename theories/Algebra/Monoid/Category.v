From Cats Require Export
  Algebra.Monoid.Core
  Algebra.Semigroup.Category.
From Cats Require Import
  Cat.Core.

Local Open Scope algebra_scope.

(** * Monoids and Single-Object Categories

    Multiplication [g ⋅ f] is categorical composition [g ∘ f]. The sole
    object is literally [unit], so no equality between arbitrary isomorphic
    objects is needed. Equality of arrows is the original setoid equality. *)

(** * 幺半群与单对象范畴

    乘法 [g ⋅ f] 解释为范畴复合 [g ∘ f]。对象类型确为 [unit]，无需等同任意
    同构对象；箭头相等直接使用原广集的相等。 *)

Program Definition MonoidCat (M : Monoid)
  : Cat
  :=
  {|Ob := unit
  ; HomSet _ _ := M
  ; id _ := 1
  ; comp _ _ _ g f := g ⋅ f
  ; comp_proper _ _ _ := mul_proper
  ; comp_id_r _ _ := mul_unit_r
  ; comp_id_l _ _ := mul_unit_l
  ; comp_assoc _ _ _ _ := mul_assoc
  |}.

Notation "'B(' M ')'" := (MonoidCat M) : cat_scope.

(** Identities extend the existing endomorphism semigroup to a monoid.
    This provides the reverse construction in particular for a specified
    singleton category, without storing composition a second time. *)

(** 恒等箭头将已有自态射半群扩展为幺半群；特别地，这给出指定单对象范畴的
    反向构造，不重复保存复合。 *)

Program Definition EndHasMonoid (C : Cat) (X : @Ob C)
  : HasMonoid (EndSemigroup C X)
  :=
  {|mul_unit := @id X
  ; isMonoid :=
      {|mul_unit_l := comp_id_l
      ; mul_unit_r := comp_id_r
      |}
  |}.

(** The existing monoid presentation reuses the selected endomorphism
    semigroup and its identity extension without rebuilding composition. *)

(** 现有幺半群呈现复用选定自态射半群及恒等扩充，不重建复合。 *)

Definition EndMonoid (C : Cat) (X : @Ob C)
  : Monoid
  := MonoidOfSemigroup (EndSemigroup C X) (EndHasMonoid C X).
