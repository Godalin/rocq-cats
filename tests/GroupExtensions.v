From Cats Require Import
  Algebra.Group.Category
  Algebra.Group.Transport
  Instance.Bool.Commutative.

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
  : @HasInverse M (Monoid_hasMagma M) (hasUnit M)
  := ltac:(typeclasses eauto).

End UnchosenExtension.

(** ** Respectfulness of a Supplied Inverse

    Fix a monoid and a candidate operation with its inverse laws. Actual
    rewriting derives respectfulness without selecting a group extension. *)

(** ** 给定逆运算的保相等性

    固定幺半群及带逆律的候选运算；无须选取群扩充即可实际重写。 *)

Section CandidateRespectfulness.
Context {M : Monoid} {i : M → M} `{Hi : !@IsInverse M i (Monoid_hasMagma M) (hasUnit M)}.

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
  := MakeMagma TokenS
    {|mul _ _ := false; mul_proper := _|}.
Next Obligation. repeat intro; exact true. Defined.

Program Definition TokenSemigroup
  : Semigroup
  := let M := TokenMagma in
     SemigroupOfMagma M
       {|mul_assoc _ _ _ := true|}.

Program Definition TokenHasUnit
  : @HasUnit TokenSemigroup (Semigroup_hasMagma TokenSemigroup)
  :=
  {|mul_unit := false
  ; isUnit :=
      {|mul_unit_l _ := true
      ; mul_unit_r _ := true
      |}
  |}.

Definition TokenMonoid
  : Monoid
  := MonoidOfSemigroup TokenSemigroup TokenHasUnit.

Program Definition TokenExtension (e t : bool)
  : @HasInverse TokenMonoid (Monoid_hasMagma TokenMonoid) (hasUnit TokenMonoid)
  :=
  {|inv _ := e
  ; isInverse :=
      {|mul_inv_l _ := t
      ; mul_inv_r _ := negb t
      |}
  |}.

Definition FalseExtension
  : @HasInverse TokenMonoid (Monoid_hasMagma TokenMonoid) (hasUnit TokenMonoid)
  := TokenExtension false false.

Definition TrueExtension
  : @HasInverse TokenMonoid (Monoid_hasMagma TokenMonoid) (hasUnit TokenMonoid)
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
  : hasInverse FirstGroup = FalseExtension.
Proof. reflexivity. Qed.

Example stored_units
  : (@mul_unit _ _ (hasUnit FirstGroup), @mul_unit _ _ (hasUnit SecondGroup)) =
      (false, false).
Proof. reflexivity. Qed.

Example stored_inverses
  : (@inv _ _ _ (hasInverse FirstGroup) true, @inv _ _ _ (hasInverse SecondGroup) true) =
      (false, true).
Proof. reflexivity. Qed.

(** Shared notation keeps the explicitly typed group's inverse even when
    another extension on the same parent is available to instance search. *)

(** 同一父结构上的另一扩充可被实例搜索找到时，共用记号仍保留显式指定群的逆。 *)

Example notation_stored_inverses
  : ((true : FirstGroup)⁻¹, (true : SecondGroup)⁻¹) = (false, true).
Proof. reflexivity. Qed.

Example stored_left_tokens
  : (@mul_inv_l _ _ _ _ (@isInverse _ _ _ (hasInverse FirstGroup)) true,
      @mul_inv_l _ _ _ _ (@isInverse _ _ _ (hasInverse SecondGroup)) true) = (false, true).
Proof. reflexivity. Qed.

Example stored_right_tokens
  : (@mul_inv_r _ _ _ _ (@isInverse _ _ _ (hasInverse FirstGroup)) false,
      @mul_inv_r _ _ _ _ (@isInverse _ _ _ (hasInverse SecondGroup)) false) = (true, false).
Proof. reflexivity. Qed.

(** The actual one-object groupoid keeps the selected inverse and laws. *)

(** 实际单对象群胚保留选定的逆及定律。 *)

Example groupoid_inverse_uses_stored_choices
  : let i := @gpd_iso (MonoidCat FirstGroup)
      (MonoidCat_IsGpd FirstGroup) tt tt true in
      (i.1, i.2) = (false, (false, true)).
Proof. reflexivity. Qed.

Example candidate_inverses_agree
  : @inv _ _ _ (hasInverse FirstGroup) ≈f @inv _ _ _ (hasInverse SecondGroup).
Proof.
  exact (inv_candidates_equiv TokenMonoid _ _
    (@isInverse TokenMonoid _ _ FalseExtension)
    (@isInverse TokenMonoid _ _ TrueExtension)).
Qed.

Fail Definition native_inverses_equal
  : @inv _ _ _ (hasInverse FirstGroup) true = @inv _ _ _ (hasInverse SecondGroup) true
  := eq_refl.

Fail Definition native_left_tokens_equal
  : @mul_inv_l _ _ _ _ (@isInverse _ _ _ (hasInverse FirstGroup)) true =
      @mul_inv_l _ _ _ _ (@isInverse _ _ _ (hasInverse SecondGroup)) true
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
Context (HA : @HasInverse MA (Monoid_hasMagma MA) (hasUnit MA)) (HB : @HasInverse MB (Monoid_hasMagma MB) (hasUnit MB)).

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

(** ** Abelian Group Views

    Both paths retain the same monoid, including its law witnesses.
    The Boolean model keeps its computation through the packed operations. *)

(** ** 阿贝尔群的父结构

    两条路径保留同一幺半群及其定律见证。布尔模型的打包运算仍可直接计算。 *)

Example ab_group_shared_monoid (A : AbGroup)
  : GroupToMonoid (AbGroupToGroup A) = CommMonoidToMonoid (AbGroupToCommMonoid A)
  := eq_refl.

Example bool_ab_group_product_inverse
  : ((true : BoolS_AbGroup) ⋅ true)⁻¹ = false
  := eq_refl.
