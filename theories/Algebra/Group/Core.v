From Cats Require Export
  Algebra.Monoid.Core.

Local Open Scope algebra_scope.

(** * Groups on Sets

    A group extends a selected monoid by computational inverses. Their
    respectfulness and coherence are derived from uniqueness, not stored. *)

(** * 广集上的群

    群为选定幺半群增加可计算的逆，逆的保相等性与相干性由唯一性导出而不另存。 *)

(** ** Inverses on a Fixed Monoid

    Fix the multiplication and its chosen unit before specifying inverse
    candidates. Every law below refers to this exact parent. *)

(** ** 固定幺半群上的逆

    先固定乘法及其选定单位元，再指定逆候选；以下每条定律均指向恰好该父结构。 *)

Section InverseExtension.
Context (M : Monoid).

(** A supplied operation is a two-sided inverse for the selected monoid. *)

(** 给定运算是选定幺半群的双侧逆。 *)

Class IsGroup (inv : M → M)
  :=
  { mul_inv_l x : inv x ⋅ x ≈S 1
  ; mul_inv_r x : x ⋅ inv x ≈S 1
  }.

(** Choose an inverse on this parent, retaining its Type-valued laws. *)

(** 在该父结构上选取逆，并保留其 Type 值定律。 *)

Class HasGroup
  :=
  { inv : M → M

  (** The laws refer to the stored inverse and the supplied monoid. *)

  (** 定律指向保存的逆及给定幺半群。 *)

  ; isGroup :: IsGroup inv
  }.

End InverseExtension.

(** Inverse laws infer their fixed parent and inverse operation. *)

(** 逆元定律推断其固定父结构和逆运算。 *)

Arguments mul_inv_l {M inv IsGroup} x.
Arguments mul_inv_r {M inv IsGroup} x.

(** A complete group owns one monoid and one inverse extension. *)

(** 完整群拥有一个幺半群及一份逆扩充。 *)

Record Group@{u p l}
  := GroupOfMonoid
  { GroupToMonoid :> Monoid@{u p l}
  ; hasGroup :: HasGroup GroupToMonoid
  }.

(** The record constructor takes its parent and witness explicitly. *)

(** 记录构造器显式接受父结构及其见证。 *)

Arguments GroupOfMonoid _ _ : clear implicits.

(** The inverse notation reads the complete group's stored choice. *)

(** 逆记号读取完整群保存的选择。 *)

Notation "x '⁻¹'" := (@inv _ (hasGroup _) x)
  (at level 1)
  : algebra_scope.

(** Candidate inverse maps agree pointwise in the specified equality;
    neither their native functions nor their law witnesses are identified. *)

(** 逆候选映射在指定相等下逐点相等，不等同原生函数或其定律见证。 *)

Lemma inv_candidates_equiv (M : Monoid)
    (i j : M → M) (Hi : IsGroup M i) (Hj : IsGroup M j)
  : i ≈f j.
Proof.
  intros x. apply (mul_inv_unique x).
  - rewrite mul_inv_l. reflexivity.
  - rewrite mul_inv_r. reflexivity.
Qed.

(** Any supplied two-sided inverse respects the monoid's specified
    equality. No selected inverse extension or complete group is needed. *)

(** 任意给定双侧逆保持幺半群指定的相等，无须选定逆扩充或完整群。 *)

Global Instance inv_proper
    {M : Monoid} {i : M → M}
    `{Hi : !IsGroup M i}
  : Proper (carrier_equiv M ==> carrier_equiv M) i.
Proof.
  intros x y H. apply (mul_inv_unique y).
  - rewrite <- H, mul_inv_l. reflexivity.
  - rewrite mul_inv_r. reflexivity.
Qed.

(** A left inverse agrees with the selected inverse using only the
    extension of the specified monoid. *)

(** 左逆仅需指定幺半群上的扩充，就与选定逆相等。 *)

Lemma inv_ext_unique (M : Monoid)
    (HG : HasGroup M) (x y : M)
    (H : (y ⋅ x) ≈S 1)
  : y ≈S @inv M HG x.
Proof.
  eapply mul_inv_unique; [exact H |].
  rewrite mul_inv_r. reflexivity.
Qed.

(** ** Inverse Laws in a Group

    Fix a setoid [G] with a chosen group structure. Derive uniqueness,
    respectfulness and the unit, involution and multiplication laws for its
    inverse. *)

(** ** 群中逆运算的定律

    固定带选定群结构的广集 [G]，由逆的唯一性导出保相等性及单位、对合和乘法定律。 *)

Section Group.
Context {G : Group}.

(** A left inverse agrees with the selected inverse. *)

(** 左逆与选定群逆相等。 *)

Lemma inv_unique (x y : G) (H : y ⋅ x ≈S 1)
  : y ≈S x⁻¹.
Proof.
  exact (inv_ext_unique (GroupToMonoid G) (hasGroup G) x y H).
Qed.

(** The unit is its own inverse. *)

(** 单位元的逆仍是单位元。 *)

Lemma inv_unit
  : (1 : G)⁻¹ ≈S 1.
Proof.
  symmetry. apply inv_unique.
  rewrite mul_unit_l. reflexivity.
Qed.

(** Taking inverses twice recovers the original element. *)

(** 连续取逆两次恢复原元素。 *)

Lemma inv_inv (x : G)
  : (x⁻¹)⁻¹ ≈S x.
Proof.
  symmetry. apply inv_unique.
  rewrite mul_inv_r. reflexivity.
Qed.

(** The inverse of a product reverses the order of its factors. *)

(** 乘积的逆反转因子次序。 *)

Lemma inv_mul (x y : G)
  : (x ⋅ y)⁻¹ ≈S y⁻¹ ⋅ x⁻¹.
Proof.
  symmetry. apply inv_unique.
  rewrite mul_assoc, <- (mul_assoc x⁻¹), mul_inv_l.
  rewrite mul_unit_l, mul_inv_l. reflexivity.
Qed.

(** Group inversion packaged as a respectful map. *)

(** 将群逆组合为保相等映射。 *)

Program Definition inv_resp
  : G →r G
  :=
  {|func x := x⁻¹
  ; func_proper :=
    @inv_proper _ _ (@isGroup _ (hasGroup G))
  |}.

End Group.
