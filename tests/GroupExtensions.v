From Cats Require Import
  Algebra.Group.Category
  Algebra.Group.Transport
  Instance.Bool.Group.

Local Open Scope algebra_scope.

(** * Fixed-Parent Group Extensions

    An inverse choice extends one exact monoid. Repacking must preserve its
    multiplication, unit, inverse and Type-valued law witnesses together. *)

(** * 固定父结构的群扩充

    逆的选择扩充恰好一个幺半群；重新包装须一同保留其乘法、单位元、逆与
    Type 值定律见证。 *)

Section UnchosenExtension.
Context (M : Monoid).

Fail Definition unchosen_group_extension
  : HasGroup M
  := ltac:(typeclasses eauto).

End UnchosenExtension.

(** ** Respectfulness of a Supplied Inverse

    Fix a monoid and a candidate operation with its inverse laws. Actual
    rewriting derives respectfulness without selecting a group extension. *)

(** ** 给定逆运算的保相等性

    固定幺半群及带逆律的候选运算；无须选取群扩充即可实际重写。 *)

Section CandidateRespectfulness.
Context {M : Monoid} {i : M → M} `{Hi : !IsGroup M i}.

(** Candidate inversion rewrites inside multiplication using derived
    respectfulness alone. *)

(** 候选逆仅使用导出的保相等性，即可在乘法内部重写。 *)

Example candidate_inverse_rewriting (x y z : M) (H : x ≈S y)
  : i x ⋅ z ≈S i y ⋅ z.
Proof. rewrite H. reflexivity. Qed.

End CandidateRespectfulness.

(** ** Competing Choices and Observable Law Witnesses

    The indiscrete bool-valued equality permits distinct native inverse
    operations and law tokens on the same monoid. Algebraic equivalence
    does not identify these computational selections. *)

(** ** 竞争选择与可观察的定律见证

    bool 值全关系相等允许同一幺半群具有原生不同的逆运算及定律标记；代数等价
    不等同这些计算选择。 *)

Program Definition TokenS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv _ _ := bool
  |}.
Next Obligation. split; repeat intro; exact true. Defined.

Program Definition TokenMagma
  : Magma
  :=
  {|MagmaToSetC := TokenS
  ; hasMagma := {|mul _ _ := false; mul_proper := _|}
  |}.
Next Obligation. repeat intro; exact true. Defined.

Program Definition TokenSemigroup
  : Semigroup
  :=
  {|SemigroupToMagma := TokenMagma
  ; isSemigroup := {|mul_assoc _ _ _ := true|}
  |}.

Program Definition TokenHasMonoid
  : HasMonoid TokenSemigroup
  :=
  {|mul_unit := false
  ; isMonoid :=
      {|mul_unit_l _ := true
      ; mul_unit_r _ := true
      |}
  |}.

Definition TokenMonoid
  : Monoid
  := MonoidOfSemigroup TokenSemigroup TokenHasMonoid.

Program Definition TokenExtension (e t : bool)
  : HasGroup TokenMonoid
  :=
  {|inv _ := e
  ; isGroup :=
      {|mul_inv_l _ := t
      ; mul_inv_r _ := negb t
      |}
  |}.

Definition FalseExtension
  : HasGroup TokenMonoid
  := TokenExtension false false.

Definition TrueExtension
  : HasGroup TokenMonoid
  := TokenExtension true true.

Local Existing Instance FalseExtension.
Local Existing Instance TrueExtension.

Definition FirstGroup
  : Group
  := GroupOfMonoid TokenMonoid FalseExtension.

Definition SecondGroup
  : Group
  := GroupOfMonoid TokenMonoid TrueExtension.

Example stored_parent
  : GroupToMonoid FirstGroup = TokenMonoid.
Proof. reflexivity. Qed.

Example stored_extension
  : hasGroup FirstGroup = FalseExtension.
Proof. reflexivity. Qed.

Example stored_units
  : (@mul_unit _ (hasMonoid FirstGroup), @mul_unit _ (hasMonoid SecondGroup)) =
      (false, false).
Proof. reflexivity. Qed.

Example stored_inverses
  : (@inv _ (hasGroup FirstGroup) true, @inv _ (hasGroup SecondGroup) true) =
      (false, true).
Proof. reflexivity. Qed.

(** Shared notation keeps the explicitly typed group's inverse even when
    another extension on the same parent is available to instance search. *)

(** 同一父结构上的另一扩充可被实例搜索找到时，共用记号仍保留显式指定群的逆。 *)

Example notation_stored_inverses
  : ((true : FirstGroup)⁻¹, (true : SecondGroup)⁻¹) = (false, true).
Proof. reflexivity. Qed.

Example stored_left_tokens
  : (@mul_inv_l _ _ (@isGroup _ (hasGroup FirstGroup)) true,
      @mul_inv_l _ _ (@isGroup _ (hasGroup SecondGroup)) true) = (false, true).
Proof. reflexivity. Qed.

Example stored_right_tokens
  : (@mul_inv_r _ _ (@isGroup _ (hasGroup FirstGroup)) false,
      @mul_inv_r _ _ (@isGroup _ (hasGroup SecondGroup)) false) = (true, false).
Proof. reflexivity. Qed.

(** The actual one-object groupoid keeps the selected inverse and laws. *)

(** 实际单对象群胚保留选定的逆及定律。 *)

Example groupoid_inverse_uses_stored_choices
  : let i := @gpd_iso (MonoidCat FirstGroup)
      (MonoidCat_IsGpd FirstGroup) tt tt true in
      (i.1, i.2) = (false, (false, true)).
Proof. reflexivity. Qed.

Example candidate_inverses_agree
  : @inv _ (hasGroup FirstGroup) ≈f @inv _ (hasGroup SecondGroup).
Proof.
  exact (inv_candidates_equiv TokenMonoid _ _
    (@isGroup TokenMonoid FalseExtension)
    (@isGroup TokenMonoid TrueExtension)).
Qed.

Fail Definition native_inverses_equal
  : @inv _ (hasGroup FirstGroup) true = @inv _ (hasGroup SecondGroup) true
  := eq_refl.

Fail Definition native_left_tokens_equal
  : @mul_inv_l _ _ (@isGroup _ (hasGroup FirstGroup)) true =
      @mul_inv_l _ _ (@isGroup _ (hasGroup SecondGroup)) true
  := eq_refl.

(** ** Strict Independent Levels

    Both carrier/equality orders and a larger law bound remain available;
    coercion to the parent recovers exactly its supplied setoid. *)

(** ** 严格独立层级

    载体／相等两种次序及更大的定律上界均可使用；父结构转换恢复恰好给定广集。 *)

Section StrictUniverses.
Universes u p l.
Constraint u < p, p < l.
Context (MA : Monoid@{u p l}) (MB : Monoid@{p u l}).
Context (HA : HasGroup MA) (HB : HasGroup MB).

Definition low_carrier_group
  : Group@{u p l}
  := GroupOfMonoid MA HA.

Definition low_equality_group
  : Group@{p u l}
  := GroupOfMonoid MB HB.

Example low_carrier_view
  : (low_carrier_group : SetC@{u p}) = (MA : SetC@{u p}).
Proof. reflexivity. Qed.

Example low_equality_view
  : (low_equality_group : SetC@{p u}) = (MB : SetC@{p u}).
Proof. reflexivity. Qed.

End StrictUniverses.
