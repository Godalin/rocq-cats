From Cats Require Import
  Algebra.Monoid.Core
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Cat.Product.Transport
  Cat.Monoidal.Cartesian.

(** * Setoid Monoids as Cartesian Monoid Objects

    This constructs an instance of the general monoidal interface from
    an existing setoid monoid. It uses the chosen set products explicitly;
    importing the module does not globally select these structures. *)

(** * 作为笛卡尔幺半群对象的广集幺半群

    从已有广集幺半群构造一般幺半接口的实例，显式使用选定的集合积；导入本模块
    不会全局选取这些结构。 *)

Definition SetCartesianMonoidal
  : MonoidalCategory SetCat
  := @CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct.

Section SetMonoid.
Context {M : SetC} (HM : Monoid M).
Local Existing Instance HM.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** The unit element gives a respectful map from the singleton set. *)

(** 单位元素给出从单元素集合出发的保相等映射。 *)

Program Definition set_monoid_unit_resp
  : UnitS →r M
  :=
  {|func _ := monoid_unit
  |}.
Next Obligation. intros x y H. reflexivity. Defined.

(** The binary operation gives a respectful map from the product set. *)

(** 二元运算给出从乘积集合出发的保相等映射。 *)

Program Definition set_monoid_mul_resp
  : M ×S M →r M
  :=
  {|func p := monoid_mul (fst p) (snd p)
  |}.
Next Obligation.
  intros [x y] [x' y'] [Hx Hy].
  exact (@monoid_mul_proper M HM x x' Hx y y' Hy).
Defined.

(** The existing algebra laws verify the internal diagrams. This does not
    duplicate the separate comparison with one-object categories. *)

(** 已有代数定律验证内部交换图表；这里不重复与单对象范畴的独立比较。 *)

Program Definition SetMonoidObject
  : MonoidObject SetCartesianMonoidal
  :=
  {|MonoidCarrier := M
  ; monoid_object_unit := set_monoid_unit_resp
  ; monoid_object_mul := set_monoid_mul_resp
  |}.
Next Obligation.
  change (set_monoid_mul_resp ∘ (set_monoid_unit_resp × id) ≈ π2).
  rewrite cross_η. intros [u x]. exact (monoid_unit_l x).
Defined.
Next Obligation.
  change (set_monoid_mul_resp ∘ (id × set_monoid_unit_resp) ≈ π1).
  rewrite cross_η. intros [x u]. exact (monoid_unit_r x).
Defined.
Next Obligation.
  change (set_monoid_mul_resp ∘ (set_monoid_mul_resp × id) ≈
    set_monoid_mul_resp ∘ (id × set_monoid_mul_resp) ∘
      (@product_assoc SetCat SetCat_HasProduct M M M).1).
  rewrite !cross_η. intros [[x y] z]. exact (monoid_assoc x y z).
Defined.

End SetMonoid.
