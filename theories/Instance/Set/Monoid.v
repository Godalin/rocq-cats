From Cats Require Import
  Algebra.Monoid.Core
  Instance.Set.Magma
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Cat.Product.Transport
  Cat.Monoidal.Cartesian.

Local Open Scope algebra_scope.

(** * Setoid Monoids as Cartesian Monoid Objects

    This constructs an instance of the general monoidal interface from
    an existing setoid monoid. It uses the chosen set products explicitly;
    importing the module does not globally select these structures. *)

(** * 作为笛卡尔幺半群对象的广集幺半群

    从已有广集幺半群构造一般幺半接口的实例，显式使用选定的集合积；导入本模块
    不会全局选取这些结构。 *)

Definition SetCartMonoidal
  : HasMonoidal SetCat
  := @CartHasMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct.

(** ** Setoid Monoids as Monoid Objects

    Fix a complete monoid [M]. Explicitly enable the setoid
    category's terminal and product choices to realize this algebra as a
    cartesian monoid object. *)

(** ** 广集幺半群作为幺半群对象

    固定完整幺半群 [M]，显式启用广集范畴的终对象和积选择，将该代数
    实现为笛卡尔幺半群对象。 *)

Section SetMonoid.
Context (M : Monoid).

Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** The unit element gives a respectful map from the singleton set. *)

(** 单位元素给出从单元素集合出发的保相等映射。 *)

Program Definition set_monoid_unit_resp
  : UnitS →r M
  :=
  {|func _ := 1
  |}.
Next Obligation. intros x y H. reflexivity. Defined.

(** The existing algebra laws verify the internal diagrams. This does not
    duplicate the separate comparison with one-object categories. *)

(** 已有代数定律验证内部交换图表；这里不重复与单对象范畴的独立比较。 *)

Program Definition SetMonoidObj
  : MonoidObj SetCartMonoidal
  :=
  {|MonoidCarrier := M
  ; monoid_object_unit := set_monoid_unit_resp
  ; monoid_object_mul := set_magma_mul_resp M
  ; isMonoidObj :=
      {|monoid_object_unit_l := _
      ; monoid_object_unit_r := _
      ; monoid_object_assoc := _
      |}
  |}.
Next Obligation.
  intros [u x].
  change (set_magma_mul_resp M
    ((set_monoid_unit_resp × id_resp) (u, x)) ≈S x).
  rewrite (cross_η (C := SetCat) (HP := SetCat_HasProduct)
    set_monoid_unit_resp id_resp (u, x)).
  change (1 ⋅ x ≈S x). rewrite mul_unit_l. reflexivity.
Defined.
Next Obligation.
  intros [x u].
  change (set_magma_mul_resp M
    ((id_resp × set_monoid_unit_resp) (x, u)) ≈S x).
  rewrite (cross_η (C := SetCat) (HP := SetCat_HasProduct)
    id_resp set_monoid_unit_resp (x, u)).
  change (x ⋅ 1 ≈S x). rewrite mul_unit_r. reflexivity.
Defined.
Next Obligation.
  intros [[x y] z].
  change (set_magma_mul_resp M
    ((set_magma_mul_resp M × id_resp) ((x, y), z)) ≈S
    set_magma_mul_resp M
      ((id_resp × set_magma_mul_resp M) (x, (y, z)))).
  rewrite (cross_η (C := SetCat) (HP := SetCat_HasProduct)
    (set_magma_mul_resp M) id_resp ((x, y), z)),
    (cross_η (C := SetCat) (HP := SetCat_HasProduct)
      id_resp (set_magma_mul_resp M) (x, (y, z))).
  change (x ⋅ y ⋅ z ≈S x ⋅ (y ⋅ z)).
  rewrite mul_assoc. reflexivity.
Defined.

End SetMonoid.
