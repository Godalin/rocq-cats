From Stdlib Require Import
  Bool.
From Cats Require Import
  Algebra.Group.Transport.
From Cats Require Import
  Instance.Bool.Group.

Local Open Scope monoid_scope.

(** * A Transport Which Changes Representatives and the Unit

    Target representatives carry an irrelevant natural tag; equality retains
    an independent Boolean witness. Negating the Boolean in both directions
    transports xor to xnor and sends the source unit [false] to [true]. The
    inverse equations hold in specified equality, not native pair equality. *)

(** * 改变代表和单位元的运输

    目标代表带一个无关的自然数标签，相等还保留独立布尔见证。双向都取布尔非，
    就把异或运输为同或，并将来源单位 [false] 送到 [true]。逆方程在指定相等
    下成立，不是原生序对相等。 *)

Definition tagged_equiv (x y : bool * nat)
  : Type
  := ((fst x = fst y) * bool)%type.

(** The equality laws preserve data; no proof irrelevance is assumed. *)

(** 相等定律保留数据，不假定证明无关性。 *)

Program Definition TaggedS
  : SetC
  :=
  {|carrier := (bool * nat)%type
  ; carrier_equiv := tagged_equiv
  |}.
Next Obligation.
  split.
  - intros x. exact (eq_refl, false).
  - intros x y [H flag]. exact (eq_sym H, negb flag).
  - intros x y z [H flag] [K flag']. exact (eq_trans H K, xorb flag flag').
Defined.

(** Forward transport forgets the tag and negates the Boolean. *)

(** 正向运输忘记标签并取布尔非。 *)

Program Definition to_bool
  : TaggedS →r BoolS
  :=
  {|func x := negb (fst x)
  |}.
Next Obligation. intros x y [H flag]. now rewrite H. Defined.

(** Returning chooses tag zero, so it cannot be a native inverse. *)

(** 返回时选择标签零，因此不可能成为原生逆。 *)

Program Definition from_bool
  : BoolS →r TaggedS
  :=
  {|func b := (negb b, 0)
  ; func_proper x y H := (f_equal negb H, false)
  |}.

(** Source recovery is native Boolean involution. *)

(** 来源恢复是原生布尔对合。 *)

Definition source_recovery
  : (to_bool ∘r from_bool) ≈f id_resp.
Proof. intros []; reflexivity. Defined.

(** Target recovery uses specified equality and retains a witness flag. *)

(** 目标恢复使用指定相等，并保留见证标记。 *)

Definition target_recovery
  : (from_bool ∘r to_bool) ≈f id_resp.
Proof. intros [[] n]; exact (eq_refl, true). Defined.

(** Explicitly select the transported group; no instance is exported. *)

(** 显式选取运输群，不导出实例。 *)

Definition TaggedGroup
  : Group TaggedS
  := GroupTransport to_bool from_bool BoolS_Group
      source_recovery target_recovery.

(** Computing all four products checks the transported operation, not just
    a proof of an inherited law. The payload is chosen by the return map. *)

(** 计算四个乘积，检查实际运输运算而非继承定律的证明；载荷由返回映射选择。 *)

Example product_table
  : (@magma_mul TaggedS TaggedGroup (false, 4) (false, 7),
     @magma_mul TaggedS TaggedGroup (false, 4) (true, 7),
     @magma_mul TaggedS TaggedGroup (true, 4) (false, 7),
     @magma_mul TaggedS TaggedGroup (true, 4) (true, 7)) =
    ((true, 0), (false, 0), (false, 0), (true, 0)).
Proof. vm_compute. reflexivity. Qed.

(** The transported unit and both inverses are actual returned values. *)

(** 运输单位元及两个逆元都是实际返回值。 *)

Example unit_inverse_values
  : (@monoid_unit TaggedS TaggedGroup,
     @group_inv TaggedS TaggedGroup (false, 19),
     @group_inv TaggedS TaggedGroup (true, 23)) =
    ((true, 0), (false, 0), (true, 0)).
Proof. vm_compute. reflexivity. Qed.

(** Target recovery does not preserve the original tag; the specified
    equality still holds with its explicitly retained Boolean witness. *)

(** 目标恢复不保留原标签，但指定相等仍成立，并带有显式保留的布尔见证。 *)

Example recovery_value_and_witness
  : (from_bool (to_bool (false, 17)), snd (target_recovery (false, 17))) =
    ((false, 0), true).
Proof. vm_compute. reflexivity. Qed.

(** The selected product and unit remain definitionally those of the
    transported parent monoid all the way through the group bundle. *)

(** 穿过群包后，选定乘积和单位仍按定义是运输父幺半群的选择。 *)

Example actual_parent
  : GroupM TaggedGroup = MonoidTransport to_bool from_bool BoolS_Group
      source_recovery target_recovery.
Proof. reflexivity. Qed.

(** Existing inverse Proper transports a genuine non-native equality,
    ignoring both different tags and different equality-witness flags. *)

(** 既有逆 Proper 运输真实的非原生相等，容许不同标签及不同相等见证标记。 *)

Definition inverse_proper_client
  : @group_inv TaggedS TaggedGroup (false, 5) ≈S
      @group_inv TaggedS TaggedGroup (false, 81)
  := @group_inv_proper TaggedS TaggedGroup
      (false, 5) (false, 81) (eq_refl, true).

(** Generic involution recovers the target element in specified equality. *)

(** 通用对合律在指定相等下恢复目标元素。 *)

Definition involution_client (x : TaggedS)
  : @group_inv TaggedS TaggedGroup (@group_inv TaggedS TaggedGroup x) ≈S x
  := @group_inv_inv TaggedS TaggedGroup x.

(** Inverse uniqueness uses the exact inherited monoid and its laws. *)

(** 逆唯一性使用原样继承的幺半群及其定律。 *)

Definition uniqueness_client (x y : TaggedS)
    (H : @magma_mul TaggedS TaggedGroup y x ≈S
      @monoid_unit TaggedS TaggedGroup)
  : y ≈S @group_inv TaggedS TaggedGroup x
  := @group_inv_unique TaggedS TaggedGroup x y H.

(** Generic inversion of a product applies without another inverse proof. *)

(** 通用乘积取逆律直接适用，不需要另一套逆证明。 *)

Definition product_inverse_client (x y : TaggedS)
  : @group_inv TaggedS TaggedGroup (@magma_mul TaggedS TaggedGroup x y) ≈S
      @magma_mul TaggedS TaggedGroup
        (@group_inv TaggedS TaggedGroup y) (@group_inv TaggedS TaggedGroup x)
  := @group_inv_mul TaggedS TaggedGroup x y.

(** The three forward comparison equations apply to the very same group. *)

(** 三个正向比较方程适用于完全相同的群。 *)

Definition product_comparison_client (x y : TaggedS)
  : to_bool (@magma_mul TaggedS TaggedGroup x y) ≈S
      @magma_mul BoolS BoolS_Group (to_bool x) (to_bool y)
  := magma_transport_map_mul to_bool from_bool BoolS_Group
      source_recovery x y.

(** Unit comparison reads the original source unit. *)

(** 单位比较读出原来源单位。 *)

Definition unit_comparison_client
  : to_bool (@monoid_unit TaggedS TaggedGroup) ≈S
      @monoid_unit BoolS BoolS_Group
  := monoid_transport_map_unit to_bool from_bool BoolS_Group
      source_recovery target_recovery.

(** Inverse comparison reads the original source inverse. *)

(** 逆比较读出原来源逆。 *)

Definition inverse_comparison_client (x : TaggedS)
  : to_bool (@group_inv TaggedS TaggedGroup x) ≈S
      @group_inv BoolS BoolS_Group (to_bool x)
  := group_transport_map_inv to_bool from_bool BoolS_Group
      source_recovery target_recovery x.

(** Native equality is intentionally too strong for recovery and unit laws. *)

(** 恢复及单位律有意不满足更强的原生相等。 *)

Fail Definition native_recovery
  : from_bool (to_bool (false, 17)) = (false, 17)
  := eq_refl.
Fail Definition native_unit_law
  : @magma_mul TaggedS TaggedGroup (@monoid_unit TaggedS TaggedGroup)
      (false, 17) = (false, 17)
  := eq_refl.
Fail Definition no_implicit_model : Group TaggedS := ltac:(typeclasses eauto).

(** Native pairs support the same one-sided associative transport, even
    though target recovery and a unit for all tags are impossible. *)

(** 原生序对仍支持同一单侧结合运输，尽管目标恢复及适用全部标签的单位不可能。 *)

Program Definition NativeTaggedS
  : SetC
  :=
  {|carrier := (bool * nat)%type
  ; carrier_equiv := eq
  ; carrier_setoid := eq_equivalence
  |}.

(** Both maps preserve native equality, independently of any inverse law. *)

(** 两映射保持原生相等，与任何逆律无关。 *)

Program Definition native_to_bool
  : NativeTaggedS →r BoolS
  :=
  {|func x := negb (fst x)
  |}.

(** The native return still chooses zero. *)

(** 原生返回仍选择零。 *)

Program Definition native_from_bool
  : BoolS →r NativeTaggedS
  :=
  {|func b := (negb b, 0)
  |}.

(** Only source recovery is available. *)

(** 仅来源恢复成立。 *)

Definition native_source_recovery
  : (native_to_bool ∘r native_from_bool) ≈f id_resp.
Proof. intros []; reflexivity. Defined.

(** The one-sided interface really constructs a semigroup in this example. *)

(** 单侧接口确实为此例构造半群。 *)

Definition NativeTaggedSemigroup
  : Semigroup NativeTaggedS
  := SemigroupTransport native_to_bool native_from_bool BoolS_Semigroup
      native_source_recovery.

(** The required law follows from that actual semigroup. *)

(** 所需定律来自该实际半群。 *)

Definition native_associativity_client (x y z : NativeTaggedS)
  : @magma_mul NativeTaggedS NativeTaggedSemigroup
      (@magma_mul NativeTaggedS NativeTaggedSemigroup x y) z ≈S
      @magma_mul NativeTaggedS NativeTaggedSemigroup x
        (@magma_mul NativeTaggedS NativeTaggedSemigroup y z)
  := @semigroup_assoc NativeTaggedS NativeTaggedSemigroup x y z.

(** Every possible left factor produces tag zero, so no left unit can
    recover the element with tag one. This is a genuine missing hypothesis. *)

(** 任意左因子都产生标签零，因此不存在能恢复标签一元素的左单位；这是真正
    缺失的前提。 *)

Example no_native_left_unit (e : NativeTaggedS)
  : @magma_mul NativeTaggedS NativeTaggedSemigroup e (false, 1%nat) ≠ (false, 1%nat).
Proof. intros H. pose proof (f_equal snd H) as K. discriminate K. Qed.

(** The omitted target recovery cannot be supplied by native reflexivity. *)

(** 缺失的目标恢复不能由原生自反性补上。 *)

Fail Definition native_target_recovery
  : (native_from_bool ∘r native_to_bool) ≈f id_resp
  := λ x, eq_refl.
Fail Definition one_sided_is_not_monoid : Monoid NativeTaggedS
  := MonoidTransport native_to_bool native_from_bool BoolS_Monoid
      native_source_recovery.
