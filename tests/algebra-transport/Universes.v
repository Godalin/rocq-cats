From Cats Require Import
  Algebra.Group.Transport.

Local Open Scope monoid_scope.

(** * Native-Size Transport Interfaces

    These clients keep all four carrier/equality levels strictly distinct.
    We also check the minimal hypotheses at each layer and native conversion
    of the immediate parent chain. No target model is enabled by import. *)

(** * 原生大小的运输接口

    以下客户端令四个载体／相等层级严格不同，同时检查各层最小前提和直接父链
    的原生定义转换。导入模块不启用任何目标模型。 *)

(** ** LowHigh: Independent Source and Target Sizes

    The source and target put equality on opposite sides of their carriers.
    Auxiliary bounds for laws remain inferred independently. *)

(** ** LowHigh：来源和目标的独立大小

    来源与目标的相等分别处于载体的相反侧，定律的辅助上界保持独立推断。 *)

Section LowHigh.
Universes l0 l1 l2 l3.
Constraint l0 < l1, l1 < l2, l2 < l3.
Context {A : SetC@{l0 l3}} {B : SetC@{l2 l1}}.
Context (f : B →r A) (g : A →r B).

(** Raw multiplication requires neither inverse equation. *)

(** 原始乘法不要求任何逆方程。 *)

Definition raw_magma (H : Magma A)
  : Magma B
  := MagmaTransport f g H.

(** Associativity needs only the source recovery equation. *)

(** 结合律只需来源恢复方程。 *)

Definition one_sided_semigroup (H : Semigroup A)
    (Hfg : (f ∘r g) ≈f id_resp)
  : Semigroup B
  := SemigroupTransport f g H Hfg.

Context (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp).

(** A monoid retains both independent specified equalities. *)

(** 幺半群保留两个独立的指定相等。 *)

Definition two_sided_monoid (H : Monoid A)
  : Monoid B
  := MonoidTransport f g H Hfg Hgf.

(** The group uses the same maps, with no new law field. *)

(** 群使用相同映射，不增加新的定律字段。 *)

Definition two_sided_group (H : Group A)
  : Group B
  := GroupTransport f g H Hfg Hgf.

(** Immediate parents are the exact preceding constructions. *)

(** 直接父结构按定义就是前一层构造。 *)

Definition group_parent (H : Group A)
  : GroupM (GroupTransport f g H Hfg Hgf) =
      MonoidTransport f g H Hfg Hgf
  := eq_refl.

(** The monoid keeps its transported semigroup. *)

(** 幺半群保留其运输半群。 *)

Definition monoid_parent (H : Monoid A)
  : MonoidSG (MonoidTransport f g H Hfg Hgf) =
      SemigroupTransport f g H Hfg
  := eq_refl.

(** The semigroup keeps its transported magma. *)

(** 半群保留其运输原群。 *)

Definition semigroup_parent (H : Semigroup A)
  : SemigroupM (SemigroupTransport f g H Hfg) = MagmaTransport f g H
  := eq_refl.

(** Selected multiplication is unchanged through the entire group chain. *)

(** 选定乘法贯穿整个群父链而不改变。 *)

Definition group_multiplication (H : Group A) (x y : B)
  : @magma_mul B (GroupTransport f g H Hfg Hgf) x y =
      g (@magma_mul A H (f x) (f y))
  := eq_refl.

(** The unit is the returned source unit. *)

(** 单位元就是返回的来源单位元。 *)

Definition group_unit (H : Group A)
  : @monoid_unit B (GroupTransport f g H Hfg Hgf) =
      g (@monoid_unit A H)
  := eq_refl.

(** The chosen inverse returns the source inverse. *)

(** 选定逆返回来源逆。 *)

Definition group_inverse (H : Group A) (x : B)
  : @group_inv B (GroupTransport f g H Hfg Hgf) x =
      g (@group_inv A H (f x))
  := eq_refl.

(** The forward map preserves multiplication with just one recovery law. *)

(** 正向映射只需一侧恢复律就保持乘法。 *)

Definition forward_multiplication (H : Magma A) (x y : B)
  : f (@magma_mul B (MagmaTransport f g H) x y) ≈S
      @magma_mul A H (f x) (f y)
  := magma_transport_map_mul f g H Hfg x y.

(** The forward map preserves the unit of the actual parent monoid. *)

(** 正向映射保持实际父幺半群的单位元。 *)

Definition forward_unit (H : Monoid A)
  : f (@monoid_unit B (MonoidTransport f g H Hfg Hgf)) ≈S
      @monoid_unit A H
  := monoid_transport_map_unit f g H Hfg Hgf.

(** The forward map preserves the actual selected group inverse. *)

(** 正向映射保持实际选定群逆。 *)

Definition forward_inverse (H : Group A) (x : B)
  : f (@group_inv B (GroupTransport f g H Hfg Hgf) x) ≈S
      @group_inv A H (f x)
  := group_transport_map_inv f g H Hfg Hgf x.

(** Inverse Proper is inherited from the existing generic theory. *)

(** 逆的 Proper 从既有通用理论继承。 *)

Definition generic_inverse_proper (H : Group A)
  : Proper (carrier_equiv B ==> carrier_equiv B)
      (@group_inv B (GroupTransport f g H Hfg Hgf))
  := @group_inv_proper B (GroupTransport f g H Hfg Hgf).

(** The same generic involution law applies to the transported structure. *)

(** 同一通用对合律适用于运输结构。 *)

Definition generic_inverse_involution (H : Group A) (x : B)
  : @group_inv B (GroupTransport f g H Hfg Hgf)
      (@group_inv B (GroupTransport f g H Hfg Hgf) x) ≈S x
  := @group_inv_inv B (GroupTransport f g H Hfg Hgf) x.

(** Unit and inverse uniqueness still use that same selected monoid. *)

(** 单位及逆唯一性仍使用同一选定幺半群。 *)

Definition generic_inverse_unique (H : Group A) (x y : B)
    (Hy : @magma_mul B (GroupTransport f g H Hfg Hgf) y x ≈S
      @monoid_unit B (GroupTransport f g H Hfg Hgf))
  : y ≈S @group_inv B (GroupTransport f g H Hfg Hgf) x
  := @group_inv_unique B (GroupTransport f g H Hfg Hgf) x y Hy.

(** Importing transport or even supplying its inputs enables no model. *)

(** 导入运输模块乃至提供其输入也不会启用模型。 *)

Fail Definition no_automatic_magma : Magma B := ltac:(typeclasses eauto).
Fail Definition no_automatic_group : Group B := ltac:(typeclasses eauto).
Fail Definition missing_source_recovery (H : Semigroup A) : Semigroup B
  := SemigroupTransport f g H.
Fail Definition missing_target_recovery (H : Monoid A) : Monoid B
  := MonoidTransport f g H Hfg.

(** Source and target law bounds can be strictly ordered either way,
    independently of all four native carrier/equality levels. *)

(** 来源和目标定律上界可严格按任一方向排列，并独立于四个原生载体／相等层级。 *)

Universes lawlo lawhi.
Constraint l3 < lawlo, lawlo < lawhi.

Definition larger_target_law_bound (H : Group@{l0 l3 lawlo} A)
  : Group@{l2 l1 lawhi} B
  := GroupTransport f g H Hfg Hgf.

(** The target law bound need not dominate the source structure bound. *)

(** 目标定律上界不必支配来源结构上界。 *)

Definition smaller_target_law_bound (H : Group@{l0 l3 lawhi} A)
  : Group@{l2 l1 lawlo} B
  := GroupTransport f g H Hfg Hgf.

End LowHigh.

(** ** HighLow: Independent Source and Target Sizes

    The source and target put equality on opposite sides of their carriers.
    Auxiliary bounds for laws remain inferred independently. *)

(** ** HighLow：来源和目标的独立大小

    来源与目标的相等分别处于载体的相反侧，定律的辅助上界保持独立推断。 *)

Section HighLow.
Universes l0 l1 l2 l3.
Constraint l0 < l1, l1 < l2, l2 < l3.
Context {A : SetC@{l3 l0}} {B : SetC@{l1 l2}}.
Context (f : B →r A) (g : A →r B).

(** Raw multiplication requires neither inverse equation. *)

(** 原始乘法不要求任何逆方程。 *)

Definition high_raw_magma (H : Magma A)
  : Magma B
  := MagmaTransport f g H.

(** Associativity needs only the source recovery equation. *)

(** 结合律只需来源恢复方程。 *)

Definition high_one_sided_semigroup (H : Semigroup A)
    (Hfg : (f ∘r g) ≈f id_resp)
  : Semigroup B
  := SemigroupTransport f g H Hfg.

Context (Hfg : (f ∘r g) ≈f id_resp) (Hgf : (g ∘r f) ≈f id_resp).

(** A monoid retains both independent specified equalities. *)

(** 幺半群保留两个独立的指定相等。 *)

Definition high_two_sided_monoid (H : Monoid A)
  : Monoid B
  := MonoidTransport f g H Hfg Hgf.

(** The group uses the same maps, with no new law field. *)

(** 群使用相同映射，不增加新的定律字段。 *)

Definition high_two_sided_group (H : Group A)
  : Group B
  := GroupTransport f g H Hfg Hgf.

(** Immediate parents are the exact preceding constructions. *)

(** 直接父结构按定义就是前一层构造。 *)

Definition high_group_parent (H : Group A)
  : GroupM (GroupTransport f g H Hfg Hgf) =
      MonoidTransport f g H Hfg Hgf
  := eq_refl.

(** The monoid keeps its transported semigroup. *)

(** 幺半群保留其运输半群。 *)

Definition high_monoid_parent (H : Monoid A)
  : MonoidSG (MonoidTransport f g H Hfg Hgf) =
      SemigroupTransport f g H Hfg
  := eq_refl.

(** The semigroup keeps its transported magma. *)

(** 半群保留其运输原群。 *)

Definition high_semigroup_parent (H : Semigroup A)
  : SemigroupM (SemigroupTransport f g H Hfg) = MagmaTransport f g H
  := eq_refl.

(** Selected multiplication is unchanged through the entire group chain. *)

(** 选定乘法贯穿整个群父链而不改变。 *)

Definition high_group_multiplication (H : Group A) (x y : B)
  : @magma_mul B (GroupTransport f g H Hfg Hgf) x y =
      g (@magma_mul A H (f x) (f y))
  := eq_refl.

(** The unit is the returned source unit. *)

(** 单位元就是返回的来源单位元。 *)

Definition high_group_unit (H : Group A)
  : @monoid_unit B (GroupTransport f g H Hfg Hgf) =
      g (@monoid_unit A H)
  := eq_refl.

(** The chosen inverse returns the source inverse. *)

(** 选定逆返回来源逆。 *)

Definition high_group_inverse (H : Group A) (x : B)
  : @group_inv B (GroupTransport f g H Hfg Hgf) x =
      g (@group_inv A H (f x))
  := eq_refl.

(** The forward map preserves multiplication with just one recovery law. *)

(** 正向映射只需一侧恢复律就保持乘法。 *)

Definition high_forward_multiplication (H : Magma A) (x y : B)
  : f (@magma_mul B (MagmaTransport f g H) x y) ≈S
      @magma_mul A H (f x) (f y)
  := magma_transport_map_mul f g H Hfg x y.

(** The forward map preserves the unit of the actual parent monoid. *)

(** 正向映射保持实际父幺半群的单位元。 *)

Definition high_forward_unit (H : Monoid A)
  : f (@monoid_unit B (MonoidTransport f g H Hfg Hgf)) ≈S
      @monoid_unit A H
  := monoid_transport_map_unit f g H Hfg Hgf.

(** The forward map preserves the actual selected group inverse. *)

(** 正向映射保持实际选定群逆。 *)

Definition high_forward_inverse (H : Group A) (x : B)
  : f (@group_inv B (GroupTransport f g H Hfg Hgf) x) ≈S
      @group_inv A H (f x)
  := group_transport_map_inv f g H Hfg Hgf x.

(** Inverse Proper is inherited from the existing generic theory. *)

(** 逆的 Proper 从既有通用理论继承。 *)

Definition high_generic_inverse_proper (H : Group A)
  : Proper (carrier_equiv B ==> carrier_equiv B)
      (@group_inv B (GroupTransport f g H Hfg Hgf))
  := @group_inv_proper B (GroupTransport f g H Hfg Hgf).

(** The same generic involution law applies to the transported structure. *)

(** 同一通用对合律适用于运输结构。 *)

Definition high_generic_inverse_involution (H : Group A) (x : B)
  : @group_inv B (GroupTransport f g H Hfg Hgf)
      (@group_inv B (GroupTransport f g H Hfg Hgf) x) ≈S x
  := @group_inv_inv B (GroupTransport f g H Hfg Hgf) x.

(** Unit and inverse uniqueness still use that same selected monoid. *)

(** 单位及逆唯一性仍使用同一选定幺半群。 *)

Definition high_generic_inverse_unique (H : Group A) (x y : B)
    (Hy : @magma_mul B (GroupTransport f g H Hfg Hgf) y x ≈S
      @monoid_unit B (GroupTransport f g H Hfg Hgf))
  : y ≈S @group_inv B (GroupTransport f g H Hfg Hgf) x
  := @group_inv_unique B (GroupTransport f g H Hfg Hgf) x y Hy.

(** Importing transport or even supplying its inputs enables no model. *)

(** 导入运输模块乃至提供其输入也不会启用模型。 *)

Fail Definition high_no_automatic_magma : Magma B := ltac:(typeclasses eauto).
Fail Definition high_no_automatic_group : Group B := ltac:(typeclasses eauto).
Fail Definition high_missing_source_recovery (H : Semigroup A) : Semigroup B
  := SemigroupTransport f g H.
Fail Definition high_missing_target_recovery (H : Monoid A) : Monoid B
  := MonoidTransport f g H Hfg.

(** Source and target law bounds can be strictly ordered either way,
    independently of all four native carrier/equality levels. *)

(** 来源和目标定律上界可严格按任一方向排列，并独立于四个原生载体／相等层级。 *)

Universes lawlo lawhi.
Constraint l3 < lawlo, lawlo < lawhi.

Definition high_larger_target_law_bound (H : Group@{l3 l0 lawlo} A)
  : Group@{l1 l2 lawhi} B
  := GroupTransport f g H Hfg Hgf.

(** The target law bound need not dominate the source structure bound. *)

(** 目标定律上界不必支配来源结构上界。 *)

Definition high_smaller_target_law_bound (H : Group@{l3 l0 lawhi} A)
  : Group@{l1 l2 lawlo} B
  := GroupTransport f g H Hfg Hgf.

End HighLow.
