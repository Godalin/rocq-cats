From Cats Require Import
  Algebra.Monoid.Core
  Instance.Set.Magma
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
  : MonoidalCat SetCat
  := @CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct.

(** ** Setoid Monoids as Monoid Objects

    Fix a monoid structure [HM] on [M]. Explicitly enable the setoid
    category's terminal and product choices to realize this algebra as a
    cartesian monoid object. *)

(** ** 广集幺半群作为幺半群对象

    固定 [M] 上的幺半群结构 [HM]，显式启用广集范畴的终对象和积选择，将该代数实现为笛卡尔幺半群对象。 *)

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

(** The existing algebra laws verify the internal diagrams. This does not
    duplicate the separate comparison with one-object categories. *)

(** 已有代数定律验证内部交换图表；这里不重复与单对象范畴的独立比较。 *)

Program Definition SetMonoidObj
  : MonoidObj SetCartesianMonoidal
  :=
  {|MonoidCarrier := M
  ; monoid_object_unit := set_monoid_unit_resp
  ; monoid_object_mul := set_magma_mul_resp HM
  |}.
Next Obligation.
  change (set_magma_mul_resp HM ∘ (set_monoid_unit_resp × id) ≈ π2).
  rewrite cross_η. intros [u x]. exact (monoid_unit_l x).
Defined.
Next Obligation.
  change (set_magma_mul_resp HM ∘ (id × set_monoid_unit_resp) ≈ π1).
  rewrite cross_η. intros [x u]. exact (monoid_unit_r x).
Defined.
Next Obligation.
  change (set_magma_mul_resp HM ∘ (set_magma_mul_resp HM × id) ≈
    set_magma_mul_resp HM ∘ (id × set_magma_mul_resp HM) ∘
      (@product_assoc SetCat SetCat_HasProduct M M M).1).
  rewrite !cross_η. intros [[x y] z]. exact (semigroup_assoc x y z).
Defined.

End SetMonoid.
