From Cats Require Export
  Algebra.Monoid.Core.

Local Open Scope monoid_scope.

(** * Groups on Sets

    A group extends a selected monoid by computational inverses. Their
    respectfulness and coherence are derived from uniqueness, not stored. *)

(** * 广集上的群

    群为选定幺半群增加可计算的逆，逆的保相等性与相干性由唯一性导出而不另存。 *)

Class Group (G : SetC)
  :=
  (** Reuse the selected monoid both as an inherited instance and as the
      unique underlying view; its setoid view then recovers [G]. *)

  (** 选定幺半群同时作为继承实例和唯一底层视图，其广集视图继而恢复 [G]。 *)

  { GroupM :> Monoid G

  (** The inverse operation is additional data on the same carrier. *)

  (** 逆运算是同一载体上的额外数据。 *)

  ; group_inv : G → G
  ; group_inv_l x : group_inv x ⋅ x ≈S 1
  ; group_inv_r x : x ⋅ group_inv x ≈S 1
  }.

Arguments GroupM {_} _.

(** Expose the same parent to instance search. The [:>] field already
    supplies the unique chain through [Monoid] to [SetC] and its carrier;
    this registration selects no further monoid. *)

(** 将同一父结构提供给实例搜索。[:>] 字段已给出经 [Monoid] 到 [SetC] 及其
    载体的唯一转换链；此注册不再选择其他幺半群。 *)

#[export] Existing Instance GroupM.

Notation "x '⁻¹'" := (group_inv x)
  (at level 9) : monoid_scope.

(** ** Inverse Laws in a Group

    Fix a setoid [G] with a chosen group structure. Derive uniqueness,
    respectfulness and the unit, involution and multiplication laws for its
    inverse. *)

(** ** 群中逆运算的定律

    固定带选定群结构的广集 [G]，由逆的唯一性导出保相等性及单位、对合和乘法定律。 *)

Section Group.
Context {G : SetC} `{HG : !Group G}.

(** A left inverse agrees with the selected group inverse. *)

(** 左逆与选定群逆相等。 *)

Lemma group_inv_unique (x y : G) (H : y ⋅ x ≈S 1)
  : y ≈S x⁻¹.
Proof. exact (monoid_inverse_unique x y x⁻¹ H (group_inv_r x)). Qed.

(** Inversion respects the specified setoid equality. *)

(** 取逆保持指定的广集相等。 *)

Global Instance group_inv_proper
  : Proper (carrier_equiv G ==> carrier_equiv G) (@group_inv G HG).
Proof.
  intros x y H. apply group_inv_unique.
  rewrite <- H. apply group_inv_l.
Qed.

(** The unit is its own inverse. *)

(** 单位元的逆仍是单位元。 *)

Lemma group_inv_unit
  : (1 : G)⁻¹ ≈S 1.
Proof. symmetry. apply group_inv_unique. apply monoid_unit_l. Qed.

(** Taking inverses twice recovers the original element. *)

(** 连续取逆两次恢复原元素。 *)

Lemma group_inv_inv (x : G)
  : (x⁻¹)⁻¹ ≈S x.
Proof. symmetry. apply group_inv_unique. apply group_inv_r. Qed.

(** The inverse of a product reverses the order of its factors. *)

(** 乘积的逆反转因子次序。 *)

Lemma group_inv_mul (x y : G)
  : (x ⋅ y)⁻¹ ≈S y⁻¹ ⋅ x⁻¹.
Proof.
  symmetry. apply group_inv_unique.
  rewrite monoid_assoc, <- (monoid_assoc x⁻¹), group_inv_l, monoid_unit_l.
  apply group_inv_l.
Qed.

(** Group inversion packaged as a respectful map. *)

(** 将群逆组合为保相等映射。 *)

Program Definition group_inv_resp
  : G →r G
  :=
  {|func x := x⁻¹
  |}.

End Group.
