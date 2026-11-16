From Cats Require Import
  Algebra.Group.Transport.

Local Open Scope algebra_scope.

(** * Transport at Strict Independent Sizes

    Check the weakest input at each layer, actual parent conversion and
    independent source/target law bounds. No historical argument order is
    required; each source is a complete mathematical object. *)

(** * 严格独立大小下的运输

    检查各层最弱输入、实际父结构转换及独立的来源／目标定律界。不维护历史参数
    次序，每个来源都是完整数学对象。 *)

(** ** LowHigh: Native Carrier and Equality Levels

    Separate all four native levels and both auxiliary law bounds. *)

(** ** LowHigh：原生载体与相等层级

    分离全部四个原生层级及两个定律辅助界。 *)

Section LowHigh.
Universes l0 l1 l2 l3 lawlo lawhi.
Constraint l0 < l1, l1 < l2, l2 < l3, l3 < lawlo, lawlo < lawhi.

(** Raw multiplication needs only a magma and two respectful maps. *)

(** 原始乘法只需原群及两个保相等映射。 *)

Definition raw_magma (A : Magma@{l0 l3 lawlo})
    (B : SetC@{l2 l1}) (f : B →r A) (g : A →r B)
  : Magma@{l2 l1 lawlo}
  := MagmaTransport A f g.

Example raw_carrier (A : Magma@{l0 l3 lawlo})
    (B : SetC@{l2 l1}) (f : B →r A) (g : A →r B)
  : (raw_magma A B f g : SetC@{l2 l1}) = B.
Proof. reflexivity. Qed.

(** Associativity needs just source recovery, without unit or inverse. *)

(** 结合律只需来源恢复，不要求单位元或逆。 *)

Definition one_sided_semigroup (A : Semigroup@{l0 l3 lawlo})
    (B : SetC@{l2 l1}) (f : B →r A) (g : A →r B)
    (Hfg : (f ∘r g) ≈f id_resp)
  : Semigroup@{l2 l1 lawlo}
  := SemigroupTransport A f g Hfg.

(** A unit needs target recovery too, but no inverse operation. *)

(** 单位元还需目标恢复，但不要求逆运算。 *)

Definition two_sided_monoid (A : Monoid@{l0 l3 lawlo})
    (B : SetC@{l2 l1}) (f : B →r A) (g : A →r B)
    (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp)
  : Monoid@{l2 l1 lawlo}
  := MonoidTransport A f g Hfg Hgf.

(** ** Selected Group Parents and Operations

    The full chain shares its transported multiplication and unit. *)

(** ** 选定群父结构与运算

    完整链共享运输后的乘法与单位。 *)

Section GroupClients.
Context (A : Group@{l0 l3 lawhi}) (B : SetC@{l2 l1}).
Context (f : B →r A) (g : A →r B).
Context (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp).

Definition transported_group
  : Group@{l2 l1 lawlo}
  := GroupTransport A f g Hfg Hgf.

Example group_parent
  : GroupToMonoid transported_group = MonoidTransport A f g Hfg Hgf.
Proof. reflexivity. Qed.

Example monoid_parent
  : MonoidToSemigroup transported_group = SemigroupTransport A f g Hfg.
Proof. reflexivity. Qed.

Example semigroup_parent
  : SemigroupToMagma transported_group = MagmaTransport A f g.
Proof. reflexivity. Qed.

Example actual_carrier
  : (transported_group : SetC@{l2 l1}) = B.
Proof. reflexivity. Qed.

Example selected_product (x y : B)
  : @mul _ (hasMagma transported_group) x y = g (@mul _ (hasMagma A) (f x) (f y)).
Proof. reflexivity. Qed.

Example selected_unit
  : @mul_unit _ (hasMonoid transported_group) =
      g (@mul_unit _ (hasMonoid A)).
Proof. reflexivity. Qed.

Example selected_inverse (x : B)
  : @inv _ (hasGroup transported_group) x = g (@inv _ (hasGroup A) (f x)).
Proof. reflexivity. Qed.

Definition forward_product (x y : B)
  : f (@mul _ (hasMagma transported_group) x y) ≈S @mul _ (hasMagma A) (f x) (f y)
  := magma_transport_map_mul A f g Hfg x y.

Definition forward_unit
  : f (@mul_unit _ (hasMonoid transported_group)) ≈S
      @mul_unit _ (hasMonoid A)
  := monoid_transport_map_unit A f g Hfg Hgf.

Definition forward_inverse (x : B)
  : f (@inv _ (hasGroup transported_group) x) ≈S @inv _ (hasGroup A) (f x)
  := group_transport_map_inv A f g Hfg Hgf x.

Definition actual_inverse_proper
  : Proper (carrier_equiv B ==> carrier_equiv B)
      (@inv _ (hasGroup transported_group))
  := @inv_proper _ _ (@isGroup _ (hasGroup transported_group)).

Definition actual_inverse_involution (x : B)
  : @inv _ (hasGroup transported_group) (@inv _ (hasGroup transported_group) x) ≈S x
  := @inv_inv transported_group x.

Definition actual_inverse_unique (x y : B)
    (H : @mul _ (hasMagma transported_group) y x ≈S
      @mul_unit _ (hasMonoid transported_group))
  : y ≈S @inv _ (hasGroup transported_group) x
  := @inv_unique transported_group x y H.

Fail Definition missing_source_recovery
  : Semigroup
  := SemigroupTransport A f g.

Fail Definition missing_target_recovery
  : Monoid
  := MonoidTransport A f g Hfg.

Fail Definition no_automatic_target_multiplication
  : HasMagma B
  := ltac:(typeclasses eauto).

End GroupClients.

(** The target law bound may also be larger than the source bound. *)

(** 目标定律界也可以大于来源界。 *)

Definition larger_target_law_bound (A : Group@{l0 l3 lawlo})
    (B : SetC@{l2 l1}) (f : B →r A) (g : A →r B)
    (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp)
  : Group@{l2 l1 lawhi}
  := GroupTransport A f g Hfg Hgf.

End LowHigh.

(** ** HighLow: Native Carrier and Equality Levels

    Separate all four native levels and both auxiliary law bounds. *)

(** ** HighLow：原生载体与相等层级

    分离全部四个原生层级及两个定律辅助界。 *)

Section HighLow.
Universes l0 l1 l2 l3 lawlo lawhi.
Constraint l0 < l1, l1 < l2, l2 < l3, l3 < lawlo, lawlo < lawhi.

(** Raw multiplication needs only a magma and two respectful maps. *)

(** 原始乘法只需原群及两个保相等映射。 *)

Definition high_raw_magma (A : Magma@{l3 l0 lawlo})
    (B : SetC@{l1 l2}) (f : B →r A) (g : A →r B)
  : Magma@{l1 l2 lawlo}
  := MagmaTransport A f g.

Example high_raw_carrier (A : Magma@{l3 l0 lawlo})
    (B : SetC@{l1 l2}) (f : B →r A) (g : A →r B)
  : (high_raw_magma A B f g : SetC@{l1 l2}) = B.
Proof. reflexivity. Qed.

(** Associativity needs just source recovery, without unit or inverse. *)

(** 结合律只需来源恢复，不要求单位元或逆。 *)

Definition high_one_sided_semigroup (A : Semigroup@{l3 l0 lawlo})
    (B : SetC@{l1 l2}) (f : B →r A) (g : A →r B)
    (Hfg : (f ∘r g) ≈f id_resp)
  : Semigroup@{l1 l2 lawlo}
  := SemigroupTransport A f g Hfg.

(** A unit needs target recovery too, but no inverse operation. *)

(** 单位元还需目标恢复，但不要求逆运算。 *)

Definition high_two_sided_monoid (A : Monoid@{l3 l0 lawlo})
    (B : SetC@{l1 l2}) (f : B →r A) (g : A →r B)
    (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp)
  : Monoid@{l1 l2 lawlo}
  := MonoidTransport A f g Hfg Hgf.

(** ** Selected Group Parents and Operations

    The full chain shares its transported multiplication and unit. *)

(** ** 选定群父结构与运算

    完整链共享运输后的乘法与单位。 *)

Section GroupClients.
Context (A : Group@{l3 l0 lawhi}) (B : SetC@{l1 l2}).
Context (f : B →r A) (g : A →r B).
Context (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp).

Definition high_transported_group
  : Group@{l1 l2 lawlo}
  := GroupTransport A f g Hfg Hgf.

Example high_group_parent
  : GroupToMonoid high_transported_group = MonoidTransport A f g Hfg Hgf.
Proof. reflexivity. Qed.

Example high_monoid_parent
  : MonoidToSemigroup high_transported_group = SemigroupTransport A f g Hfg.
Proof. reflexivity. Qed.

Example high_semigroup_parent
  : SemigroupToMagma high_transported_group = MagmaTransport A f g.
Proof. reflexivity. Qed.

Example high_actual_carrier
  : (high_transported_group : SetC@{l1 l2}) = B.
Proof. reflexivity. Qed.

Example high_selected_product (x y : B)
  : @mul _ (hasMagma high_transported_group) x y = g (@mul _ (hasMagma A) (f x) (f y)).
Proof. reflexivity. Qed.

Example high_selected_unit
  : @mul_unit _ (hasMonoid high_transported_group) =
      g (@mul_unit _ (hasMonoid A)).
Proof. reflexivity. Qed.

Example high_selected_inverse (x : B)
  : @inv _ (hasGroup high_transported_group) x = g (@inv _ (hasGroup A) (f x)).
Proof. reflexivity. Qed.

Definition high_forward_product (x y : B)
  : f (@mul _ (hasMagma high_transported_group) x y) ≈S @mul _ (hasMagma A) (f x) (f y)
  := magma_transport_map_mul A f g Hfg x y.

Definition high_forward_unit
  : f (@mul_unit _ (hasMonoid high_transported_group)) ≈S
      @mul_unit _ (hasMonoid A)
  := monoid_transport_map_unit A f g Hfg Hgf.

Definition high_forward_inverse (x : B)
  : f (@inv _ (hasGroup high_transported_group) x) ≈S @inv _ (hasGroup A) (f x)
  := group_transport_map_inv A f g Hfg Hgf x.

Definition high_actual_inverse_proper
  : Proper (carrier_equiv B ==> carrier_equiv B)
      (@inv _ (hasGroup high_transported_group))
  := @inv_proper _ _ (@isGroup _ (hasGroup high_transported_group)).

Definition high_actual_inverse_involution (x : B)
  : @inv _ (hasGroup high_transported_group) (@inv _ (hasGroup high_transported_group) x) ≈S x
  := @inv_inv high_transported_group x.

Definition high_actual_inverse_unique (x y : B)
    (H : @mul _ (hasMagma high_transported_group) y x ≈S
      @mul_unit _ (hasMonoid high_transported_group))
  : y ≈S @inv _ (hasGroup high_transported_group) x
  := @inv_unique high_transported_group x y H.

Fail Definition high_missing_source_recovery
  : Semigroup
  := SemigroupTransport A f g.

Fail Definition high_missing_target_recovery
  : Monoid
  := MonoidTransport A f g Hfg.

Fail Definition high_no_automatic_target_multiplication
  : HasMagma B
  := ltac:(typeclasses eauto).

End GroupClients.

(** The target law bound may also be larger than the source bound. *)

(** 目标定律界也可以大于来源界。 *)

Definition high_larger_target_law_bound (A : Group@{l3 l0 lawlo})
    (B : SetC@{l1 l2}) (f : B →r A) (g : A →r B)
    (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp)
  : Group@{l1 l2 lawhi}
  := GroupTransport A f g Hfg Hgf.

End HighLow.
