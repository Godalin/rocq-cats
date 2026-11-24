From Cats Require Export
  Algebra.Monoid.Core.

Local Open Scope algebra_scope.

(** * Groups on Sets

    A group extends a selected monoid by computational inverses. Their
    respectfulness and coherence are derived from uniqueness, not stored. *)

(** * 广集上的群

    群为选定幺半群增加可计算的逆，逆的保相等性与相干性由唯一性导出而不另存。 *)

(** A specified operation inverts the selected multiplication and unit. *)

(** 指定运算给出选定乘法和单位元上的逆。 *)

Minks.Mixin IsInverse (S : SetC) (i : S → S)
  extends HasUnit S
  :=
  { mul_inv_l x : mul (i x) x ≈S mul_unit
  ; mul_inv_r x : mul x (i x) ≈S mul_unit
  }.

(** Choose an inverse and its laws on the same multiplication and unit. *)

(** 在同一乘法和单位元上选取逆及其定律。 *)

Minks.Mixin HasInverse (S : SetC)
  extends HasUnit S
  :=
  { inv : S → S
  ; isInverse :: @IsInverse S inv hasMagma hasUnit
  }.

Arguments mul_inv_l {_ _ _ _ _} x.
Arguments mul_inv_r {_ _ _ _ _} x.

(** Store one setoid with its multiplication, associativity, unit and inverse. *)

(** 将一份广集及其乘法、结合律、单位元和逆元平铺保存。 *)

Minks.Struct Group
  extends Monoid
  with  hasInverse as hasInverse : HasInverse.

Notation "x '⁻¹'" := (@inv _ _ _ (hasInverse _) x)
  (at level 1)
  : algebra_scope.

(** Candidate inverse maps agree pointwise in the specified equality;
    neither their native functions nor their law witnesses are identified. *)

(** 逆候选映射在指定相等下逐点相等，不等同原生函数或其定律见证。 *)

Lemma inv_candidates_equiv (M : Monoid)
    (i j : M → M)
    (Hi : @IsInverse M i (Monoid_hasMagma M) (hasUnit M))
    (Hj : @IsInverse M j (Monoid_hasMagma M) (hasUnit M))
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
    `{Hi : !@IsInverse M i (Monoid_hasMagma M) (hasUnit M)}
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
    (HG : @HasInverse M (Monoid_hasMagma M) (hasUnit M)) (x y : M)
    (H : (y ⋅ x) ≈S 1)
  : y ≈S @inv _ _ _ HG x.
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
  exact (inv_ext_unique (GroupToMonoid G) (hasInverse G) x y H).
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
    @inv_proper (GroupToMonoid G) _ (@isInverse _ _ _ (hasInverse G))
  |}.

End Group.
