From Cats Require Export
  Instance.Bool.CocycleSphere
  Instance.Set.Simplicial.Cocycle.SphereGroup.

Local Existing Instance BoolS_Group.
Local Existing Instance BoolS_IsCommutativeMonoid.
Local Open Scope monoid_scope.

(** * The Order-Two Group of Boolean Sphere Classes

    The previous chapter supplied a sphere not related to the constant
    one. The actual tetrahedron composition now equips these same classes
    with a group: coefficients compute xor, the constant sphere is the
    unit, and every class is its own inverse. The nonzero sphere therefore
    has order two in this explicitly constructed group.

    The next chapter
    %\coqref{Cats.Instance.Bool.CocycleSphereCylinder.bool cocycle sphere no relative cylinder}
    {%[bool_cocycle_sphere_no_relative_cylinder]%}% proves non-contraction
    by a full relative cylinder. Invariance under homotopy equivalence
    remains required before the broader higher-homotopy distinction. *)

(** * 布尔球面类的二阶群

    前章给出不能联系到常值球面的球面。现在，实际四面体合成为同一批类赋予群：
    系数计算为异或，常值球面为单位，每个类自逆。因此，非零球面在这个显式
    构造的群中具有二阶。

    下一章
    %\coqref{Cats.Instance.Bool.CocycleSphereCylinder.bool cocycle sphere no relative cylinder}
    {%[bool_cocycle_sphere_no_relative_cylinder]%}% 证明完整相对柱也不能将其
    收缩。更广的高阶同伦区别仍需同伦等价下的不变性。 *)

(** Select the group on the existing class setoid without global enabling. *)

(** 选择既有类广集上的群，不全局启用。 *)

Definition BoolCocycleSphereClassS_Group
  : Group BoolCocycleSphereClassS
  := cocycle_two_sphere_Group.

(** Commutativity refers to that group's very same monoid parent. *)

(** 交换性针对该群的同一个幺半群父结构。 *)

Definition BoolCocycleSphereClassS_IsCommutativeMonoid
  : @IsCommutativeMonoid BoolCocycleSphereClassS
      (GroupM BoolCocycleSphereClassS_Group)
  := cocycle_two_sphere_IsCommutativeMonoid.

(** The inverse coefficient is the original Boolean coefficient. *)

(** 逆系数就是原布尔系数。 *)

Lemma bool_cocycle_sphere_class_inv (x : BoolCocycleSphereClassS)
  : cocycle_two_sphere_inv x ≈S x.
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  rewrite cocycle_two_sphere_inv_value. reflexivity.
Defined.

(** Two copies of the nonzero class compose to the constant sphere. *)

(** 非零类的两个副本合成为常值球面。 *)

Lemma bool_cocycle_sphere_square
  : cocycle_two_sphere_mul bool_cocycle_sphere bool_cocycle_sphere ≈S
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)
        : BoolCocycleSphereClassS).
Proof.
  apply (snd (cocycle_two_sphere_class_eq_iff _ _)).
  rewrite cocycle_two_sphere_mul_value. reflexivity.
Defined.

(** The order-two law has a retained tetrahedron with exactly these faces. *)

(** 二阶定律具有恰以这些球面为面的保留四面体。 *)

Definition BoolCocycleSphereSquare
  : TwoSphereComposite BoolCocycleModel (two_cocycle_simplex_unit 0)
      bool_cocycle_sphere bool_cocycle_sphere
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0))
  := CocycleTwoSphereComposite bool_cocycle_sphere bool_cocycle_sphere
      (two_sphere_base BoolCocycleModel (two_cocycle_simplex_unit 0)) eq_refl.
