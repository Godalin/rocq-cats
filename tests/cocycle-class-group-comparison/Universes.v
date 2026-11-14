From Cats Require Import
  Instance.Set.Simplicial.Cocycle.SphereKanGroup.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.
Local Open Scope monoid_scope.

(** * Independent Coefficient, Simplex and Common Isomorphism Sizes

    Probe opposite coefficient carrier/equality orders and lower/higher
    ambient equality. Product comparisons need only a monoid and their
    one three-horn choice; inverse comparison only a group and its own
    left-candidate choice. Common isomorphism bounds are raised separately. *)

(** * 独立的系数、单形与共同同构大小

    检查相反系数载体／相等次序及较低／较高环境相等。乘积比较只需幺半群和
    自身三维选择，逆比较只需群及自身左候选选择；共同同构界分别向上提升。 *)

(** ** Strictly Separated Bounds

    Fix seven increasing levels; native sizes lie below the simplex sizes
    and both common lift bounds. No equality of these bounds is permitted. *)

(** ** 严格分离的界

    固定七个递增层级，原生大小低于单形大小及两个共同提升界，不允许等同这些界。 *)

Section StrictSizes.
Universes e h l u p v q.
Constraint e < h, h < l, l < u, u < p, p < v, v < q.

(** Product comparison needs no group, commutativity or four-horn choice. *)

(** 乘积比较不需群、交换性或四维选择。 *)

Definition lower_product
    (M : SetC@{h e}) `{HM : !Monoid M}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 3 fin_first⁺⁺)
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H x y ≈S
      cocycle_two_sphere_mul x y
  := cocycle_kan_mul_eq H x y.

(** Decoding preserves the actual product at the native coefficient sizes. *)

(** 读取在原生系数大小下保持实际乘积。 *)

Definition lower_decode
    (M : SetC@{h e}) `{HM : !Monoid M}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 3 fin_first⁺⁺)
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : cocycle_two_sphere_class_value_resp
      (two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H x y) ≈S
      cocycle_two_sphere_class_value_resp x ⋅
        cocycle_two_sphere_class_value_resp y
  := cocycle_kan_mul_value H x y.

(** Encoding preserves the product without any four-horn selection. *)

(** 编码保持乘积，不需任何四维选择。 *)

Definition lower_encode
    (M : SetC@{h e}) `{HM : !Monoid M}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 3 fin_first⁺⁺)
    (a b : M)
  : cocycle_two_sphere_class_resp (a ⋅ b) ≈S
      two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H
        (cocycle_two_sphere_class_resp a) (cocycle_two_sphere_class_resp b)
  := cocycle_kan_class_mul H a b.

(** Inverse comparison needs only its own three-horn selection. *)

(** 逆比较仅需自身三维选择。 *)

Definition lower_inverse
    (M : SetC@{h e}) `{HG : !Group M}
    (K : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 3 fin_first⁺⁺⁺)
    (x : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : ((@SphereKanLeftInverse _ (two_cocycle_simplex_unit 0) K x).1 : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0)) ≈S
      cocycle_two_sphere_inv x
  := cocycle_kan_left_inverse_eq K x.

(** The actual inverse decodes at independent coefficient sizes. *)

(** 实际逆在独立系数大小下读取。 *)

Definition lower_inverse_value
    (M : SetC@{h e}) `{HG : !Group M}
    (K : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 3 fin_first⁺⁺⁺)
    (x : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : cocycle_two_sphere_class_value_resp
      (@SphereKanLeftInverse _ (two_cocycle_simplex_unit 0) K x).1 ≈S
      (cocycle_two_sphere_class_value_resp x)⁻¹
  := cocycle_kan_left_inverse_value K x.

(** Raw model commutativity needs no group or four-horn choice. *)

(** 模型原始交换律不需群或四维选择。 *)

Definition lower_commutative_product
    (M : SetC@{h e}) `{HM : !Monoid M}
    `{HC : !IsCommutativeMonoid M}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 3 fin_first⁺⁺)
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H x y ≈S
      two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H y x
  := cocycle_kan_mul_comm H x y.

(** The property refers to exactly the generic selected class monoid. *)

(** 性质恰针对通用选定类幺半群。 *)

Definition lower_commutative_monoid
    (M : SetC@{h e}) `{HM : !Monoid M}
    `{HC : !IsCommutativeMonoid M}
    `{HX2 : !HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) 3 fin_first⁺⁺)
  : @IsCommutativeMonoid (TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
      (TwoSphereClassMonoid _ (two_cocycle_simplex_unit 0) H)
  := cocycle_kan_IsCommutativeMonoid H.

(** Reuse the existing isomorphism at independent common upward bounds. *)

(** 在独立共同向上界复用既有同构。 *)

Definition lower_common_iso
    (M : SetC@{h e}) `{HM : !Monoid M}
  : LiftS@{_ _ v q} (TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u l _ _ _ _ _})
      (two_cocycle_simplex_unit 0)) ≅[SetCat]
      LiftS@{_ _ v q} M
  := cocycle_two_sphere_class_iso.

(** Product comparison needs no group, commutativity or four-horn choice. *)

(** 乘积比较不需群、交换性或四维选择。 *)

Definition higher_product
    (M : SetC@{e h}) `{HM : !Monoid M}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 fin_first⁺⁺)
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H x y ≈S
      cocycle_two_sphere_mul x y
  := cocycle_kan_mul_eq H x y.

(** Decoding preserves the actual product at the native coefficient sizes. *)

(** 读取在原生系数大小下保持实际乘积。 *)

Definition higher_decode
    (M : SetC@{e h}) `{HM : !Monoid M}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 fin_first⁺⁺)
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : cocycle_two_sphere_class_value_resp
      (two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H x y) ≈S
      cocycle_two_sphere_class_value_resp x ⋅
        cocycle_two_sphere_class_value_resp y
  := cocycle_kan_mul_value H x y.

(** Encoding preserves the product without any four-horn selection. *)

(** 编码保持乘积，不需任何四维选择。 *)

Definition higher_encode
    (M : SetC@{e h}) `{HM : !Monoid M}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 fin_first⁺⁺)
    (a b : M)
  : cocycle_two_sphere_class_resp (a ⋅ b) ≈S
      two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H
        (cocycle_two_sphere_class_resp a) (cocycle_two_sphere_class_resp b)
  := cocycle_kan_class_mul H a b.

(** Inverse comparison needs only its own three-horn selection. *)

(** 逆比较仅需自身三维选择。 *)

Definition higher_inverse
    (M : SetC@{e h}) `{HG : !Group M}
    (K : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 fin_first⁺⁺⁺)
    (x : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : ((@SphereKanLeftInverse _ (two_cocycle_simplex_unit 0) K x).1 : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0)) ≈S
      cocycle_two_sphere_inv x
  := cocycle_kan_left_inverse_eq K x.

(** The actual inverse decodes at independent coefficient sizes. *)

(** 实际逆在独立系数大小下读取。 *)

Definition higher_inverse_value
    (M : SetC@{e h}) `{HG : !Group M}
    (K : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 fin_first⁺⁺⁺)
    (x : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : cocycle_two_sphere_class_value_resp
      (@SphereKanLeftInverse _ (two_cocycle_simplex_unit 0) K x).1 ≈S
      (cocycle_two_sphere_class_value_resp x)⁻¹
  := cocycle_kan_left_inverse_value K x.

(** Raw model commutativity needs no group or four-horn choice. *)

(** 模型原始交换律不需群或四维选择。 *)

Definition higher_commutative_product
    (M : SetC@{e h}) `{HM : !Monoid M}
    `{HC : !IsCommutativeMonoid M}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 fin_first⁺⁺)
    (x y : TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
  : two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H x y ≈S
      two_sphere_kan_mul _ (two_cocycle_simplex_unit 0) H y x
  := cocycle_kan_mul_comm H x y.

(** The property refers to exactly the generic selected class monoid. *)

(** 性质恰针对通用选定类幺半群。 *)

Definition higher_commutative_monoid
    (M : SetC@{e h}) `{HM : !Monoid M}
    `{HC : !IsCommutativeMonoid M}
    `{HX2 : !HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 4 fin_first⁺⁺⁺}
    `{HX4 : !HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 4 fin_first⁺⁺⁺⁺}
    (H : HasHornFillers
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 3 fin_first⁺⁺)
  : @IsCommutativeMonoid (TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0))
      (TwoSphereClassMonoid _ (two_cocycle_simplex_unit 0) H)
  := cocycle_kan_IsCommutativeMonoid H.

(** Reuse the existing isomorphism at independent common upward bounds. *)

(** 在独立共同向上界复用既有同构。 *)

Definition higher_common_iso
    (M : SetC@{e h}) `{HM : !Monoid M}
  : LiftS@{_ _ q v} (TwoSphereClassS
      (Z²(M) : Fct (Δ^op) SetCat@{u p _ _ _ _ _})
      (two_cocycle_simplex_unit 0)) ≅[SetCat]
      LiftS@{_ _ q v} M
  := cocycle_two_sphere_class_iso.

End StrictSizes.
