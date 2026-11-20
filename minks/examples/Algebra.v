From Stdlib Require Import Utf8.
From Minks Require Import all.

Set Universe Polymorphism.

(** * A flat hierarchy experiment

    Mixins name their exact dependencies. Complete records and forgetful
    maps are generated below from the same component graph. *)

(** * 平铺层级实验

    Mixin 指明其依赖的具体选择。完整记录与忘却映射由同一份组件图生成。 *)

(** Choose a Type-valued equivalence on the external carrier. *)

(** 在外部载体上选取 Type 值等价关系。 *)

Class HasEquiv@{u e} (A : Type@{u})
  :=
  { equiv : A → A → Type@{e}
  ; equiv_refl : ∀ x, equiv x x
  ; equiv_sym : ∀ x y, equiv x y → equiv y x
  ; equiv_trans : ∀ x y z, equiv x y → equiv y z → equiv x z
  }.

Arguments equiv {_ _} _ _.

(** Choose a multiplication respectful for the specified equivalence. *)

(** 选取保持指定等价关系的乘法。 *)

Class HasMagma@{u e} (A : Type@{u}) `(E : !HasEquiv@{u e} A)
  :=
  { binop : A → A → A
  ; mul : A → A → A := binop
  ; mul_proper
    : ∀ x x' y y',
      equiv x x' → equiv y y' → equiv (mul x y) (mul x' y')
  }.

Arguments mul {_ _ _} _ _.

(** Choose a point without requiring an equivalence on its carrier. *)

(** 选取一个点，无须给载体指定等价关系。 *)

Class HasPoint@{u} (A : Type@{u})
  :=
  { point : A
  }.

Arguments point {_ _}.

(** Require associativity of the selected multiplication. *)

(** 要求所选乘法满足结合律。 *)

Class IsSemigroup@{u e} (A : Type@{u}) `(E : !HasEquiv@{u e} A)
    `(M : !HasMagma A E)
  :=
  { mul_assoc : ∀ x y z,
      equiv (mul (mul x y) z) (mul x (mul y z))
  }.

(** Choose a unit for the selected multiplication and witness both unit laws. *)

(** 为选定乘法选取单位元，并提供左右单位律的见证。 *)

Class HasUnit@{u e} (A : Type@{u}) `(E : !HasEquiv@{u e} A)
    `(M : !HasMagma A E)
  :=
  { unit : A
  ; mul_unit_l : ∀ x, equiv (mul unit x) x
  ; mul_unit_r : ∀ x, equiv (mul x unit) x
  }.

(** Declare the component dependencies and the inheritance graph. *)

(** 声明组件依赖及继承图。 *)

Minks.Struct SetC
  with  hasEquiv : HasEquiv [carrier].
Minks.Struct Magma extends SetC
  with  hasMagma : HasMagma [carrier, hasEquiv].
Minks.Struct PointedSetC extends SetC
  with  hasPoint : HasPoint [carrier].
Minks.Struct Semigroup extends Magma
  with  isSemigroup : IsSemigroup [carrier, hasEquiv, hasMagma].
Minks.Struct PointedMagma extends Magma, PointedSetC.
Minks.Struct UMagma extends Magma
  with  hasUnit : HasUnit [carrier, hasEquiv, hasMagma].
Minks.Struct Monoid extends Semigroup, UMagma.

Minks.Inspect Monoid.

Print MakeMonoid.

(** Both paths use the same stored carrier, setoid and multiplication. *)

(** 两条路径读取同一份载体、广集相等及乘法。 *)

Definition pointed_magma_set_coherence (M : PointedMagma)
  : MagmaToSetC (PointedMagmaToMagma M)
    = PointedSetCToSetC (PointedMagmaToPointedSetC M)
  := eq_refl.

Definition monoid_magma_coherence (M : Monoid)
  : SemigroupToMagma (MonoidToSemigroup M)
    = UMagmaToMagma (MonoidToUMagma M)
  := eq_refl.

(** Use the original class method on the selected multiplication. *)

(** 直接使用类中的结合律，读取完整结构选定的乘法。 *)

Definition inferred_assoc (M : Monoid) (x y z : M)
  : equiv (mul (mul x y) z) (mul x (mul y z))
  := mul_assoc x y z.

Definition inferred_assoc_uses_fields (M : Monoid) (x y z : M)
  : inferred_assoc M x y z =
      @mul_assoc M (Monoid_hasEquiv M) (Monoid_hasMagma M)
        (Monoid_isSemigroup M) x y z
  := eq_refl.

(** Use the unit and its law through the same selected mixin. *)

(** 通过同一份选定组件使用单位元及其定律。 *)

Definition inferred_unit_l (M : Monoid) (x : M)
  : equiv (mul unit x) x
  := mul_unit_l x.

Definition inferred_unit_l_uses_field (M : Monoid) (x : M)
  : inferred_unit_l M x =
      @mul_unit_l M (Monoid_hasEquiv M) (Monoid_hasMagma M)
        (Monoid_hasUnit M) x
  := eq_refl.

(** A matching type does not identify two independently declared slots. *)

(** 两个组件类型相同，也不会因此被识别为同一份选择。 *)

Minks.Struct TwoPoints extends PointedSetC
  with  hasOtherPoint : HasPoint [carrier].

(** Two unlabelled point choices do not provide a default instance. *)

(** 同类的两个点不会提供默认基点实例。 *)

Fail Definition ambiguous_point (P : TwoPoints)
  : HasPoint P
  := ltac:(typeclasses eauto).

(** ** Independent point choices

    On one boolean setoid, choose two point mixins and check which
    choice each projection reads. *)

(** ** 独立的基点选择

    在同一布尔广集上选取两个基点组件，检查各投影读取哪一份选择。 *)

Section DistinctPoints.
Context (E : HasEquiv bool)
    (P Q : HasPoint bool).

Definition independent_points
  : TwoPoints
  := MakeTwoPoints bool E P Q.

Definition first_point_computes
  : @point bool
      (PointedSetC_hasPoint (TwoPointsToPointedSetC independent_points))
    = @point bool P
  := eq_refl.

Definition second_point_computes
  : @point bool (TwoPoints_hasOtherPoint independent_points) = @point bool Q
  := eq_refl.

End DistinctPoints.

(** Check that the carrier and equivalence witnesses admit either strict
    ordering. The arity here is specific to the experimental generator. *)

(** 检查载体与相等见证可按两种严格次序实例化。这里的宇宙参数位置仅用于实验。 *)

Definition wider_equivalence@{u e r | u < e, e < r}
    (A : Type@{u}) (E : HasEquiv@{u e} A) (M : HasMagma@{u e} A E)
  : Magma@{u r u e}
  := MakeMagma A E M.

Definition wider_carrier@{u e r | e < u, u < r}
    (A : Type@{u}) (E : HasEquiv@{u e} A) (M : HasMagma@{u e} A E)
  : Magma@{u r u e}
  := MakeMagma A E M.
