From Cats Require Import
  Cat.Core
  Algebra.Monoid.Category
  Algebra.Monoid.Transport
  Instance.Bool.Group.

Local Open Scope monoid_scope.

(** * Complete Monoids and Fixed-Parent Choices

    Complete objects own their carrier. Extensions remain indexed by one
    selected parent; importing a model must not select an extension. *)

(** * 完整幺半群与固定父结构选择

    完整对象拥有其载体；扩充仍以一个选定父结构索引，导入模型不应选择扩充。 *)

Section UnchosenExtension.
Context (SG : Semigroup).

Fail Definition unchosen_monoid_extension
  : HasMonoid SG
  := ltac:(typeclasses eauto).

End UnchosenExtension.

(** ** Two Extensions of One Parent

    Both choices stay available; packing reads the supplied evidence. *)

(** ** 同一父结构的两份扩充

    两份选择同时存在，打包只读取给定见证。 *)

Section IndependentChoices.
Context (SG : Semigroup) (H K : HasMonoid SG).

Example first_parent_is_preserved
  : MonoidToSemigroup (MonoidFromExtension SG H) = SG.
Proof. reflexivity. Qed.

Example first_extension_is_preserved
  : hasMonoid (MonoidFromExtension SG H) = H.
Proof. reflexivity. Qed.

Example first_unit_is_selected
  : @monoid_unit _ (hasMonoid (MonoidFromExtension SG H)) =
      @monoid_unit SG H.
Proof. reflexivity. Qed.

Example selected_units_are_equivalent
  : @monoid_unit SG H ≈S @monoid_unit SG K.
Proof.
  exact (units_equiv SG _ _ (@isMonoid SG H) (@isMonoid SG K)).
Qed.

End IndependentChoices.

(** ** Distinct Computational Choices

    Bool-valued indiscrete equality permits different native units and law
    tokens. Competing local instances must not replace stored selections. *)

(** ** 不同计算选择

    bool 值全关系相等允许原生不同的单位及定律标记；竞争局部实例不能替换保存
    的选择。 *)

Program Definition IndiscreteBoolS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv _ _ := bool
  |}.
Next Obligation. split; repeat intro; exact true. Defined.

Program Definition ConstantBoolMagma
  : Magma
  :=
  {|MagmaToSetC := IndiscreteBoolS
  ; hasMagma :=
      {|mul _ _ := false
      ; mul_proper _ _ _ _ _ _ := true
      |}
  |}.

Program Definition ConstantBoolSemigroup
  : Semigroup
  :=
  {|SemigroupToMagma := ConstantBoolMagma
  ; isSemigroup := {|mul_assoc _ _ _ := true|}
  |}.

(** Different operations and associativity witnesses on the same carrier
    remain separate computational choices. *)

(** 同一载体上的不同运算与结合律见证仍是分离的计算选择。 *)

Program Definition TrueMultiplication
  : HasMagma IndiscreteBoolS
  :=
  {|mul _ _ := true
  ; mul_proper _ _ _ _ _ _ := false
  |}.

Definition TrueMagma
  : Magma
  := MagmaFromExtension IndiscreteBoolS TrueMultiplication.

Local Existing Instance TrueMultiplication.

Program Definition OtherAssociativity
  : IsSemigroup ConstantBoolMagma
  := {|mul_assoc _ _ _ := false|}.

Local Existing Instance OtherAssociativity.

Definition OtherSemigroup
  : Semigroup
  := SemigroupFromProperty ConstantBoolMagma OtherAssociativity.

Example stored_multiplications_compute
  : (@mul _ (hasMagma ConstantBoolMagma) false false,
      @mul _ (hasMagma TrueMagma) false false) = (false, true).
Proof. reflexivity. Qed.

Example stored_associativities_compute
  : (@mul_assoc _ (isSemigroup ConstantBoolSemigroup) true false true,
      @mul_assoc _ (isSemigroup OtherSemigroup) true false true) = (true, false).
Proof. reflexivity. Qed.

Example inherited_magma_carrier
  : (ConstantBoolSemigroup : SetC) = IndiscreteBoolS.
Proof. reflexivity. Qed.

Program Definition BoolUnitExtension (e t : bool)
  : HasMonoid ConstantBoolSemigroup
  :=
  {|monoid_unit := e
  ; isMonoid :=
      {|mul_unit_l _ := t
      ; mul_unit_r _ := negb t
      |}
  |}.

Definition FalseUnit
  : HasMonoid ConstantBoolSemigroup
  := BoolUnitExtension false false.

Definition TrueUnit
  : HasMonoid ConstantBoolSemigroup
  := BoolUnitExtension true true.

Local Existing Instance FalseUnit.
Local Existing Instance TrueUnit.

Definition FirstMonoid
  : Monoid
  := MonoidFromExtension ConstantBoolSemigroup FalseUnit.

Definition SecondMonoid
  : Monoid
  := MonoidFromExtension ConstantBoolSemigroup TrueUnit.

Example stored_units_compute
  : (@monoid_unit _ (hasMonoid FirstMonoid),
      @monoid_unit _ (hasMonoid SecondMonoid)) = (false, true).
Proof. reflexivity. Qed.

Example stored_left_laws_compute
  : (@mul_unit_l _ _ (@isMonoid _ (hasMonoid FirstMonoid)) false,
      @mul_unit_l _ _ (@isMonoid _ (hasMonoid SecondMonoid)) false) =
      (false, true).
Proof. reflexivity. Qed.

Example stored_right_laws_compute
  : (@mul_unit_r _ _ (@isMonoid _ (hasMonoid FirstMonoid)) true,
      @mul_unit_r _ _ (@isMonoid _ (hasMonoid SecondMonoid)) true) =
      (true, false).
Proof. reflexivity. Qed.

(** The actual category constructor reads these same stored law tokens. *)

(** 实际范畴构造器读取同一批保存的定律标记。 *)

Example category_laws_use_stored_choices
  : (@comp_id_l (MonoidCat FirstMonoid) tt tt false,
      @comp_id_r (MonoidCat FirstMonoid) tt tt false,
      @comp_assoc (MonoidCat FirstMonoid) tt tt tt tt false false false) =
      (false, true, true).
Proof. reflexivity. Qed.

Fail Definition native_units_equal
  : @monoid_unit _ (hasMonoid FirstMonoid) =
      @monoid_unit _ (hasMonoid SecondMonoid)
  := eq_refl.

(** ** Concrete Clients and Independent Sizes

    Actual model projections compute. Strict sizes concern mathematical
    independence, not historical universe-argument positions. *)

(** ** 具体客户端与独立大小

    实际模型投影可计算；严格大小检查数学上的独立性，不维护历史宇宙参数位置。 *)

Example xor_unit_computes
  : @monoid_unit _ (hasMonoid BoolS_Monoid) = false.
Proof. reflexivity. Qed.

Example endomorphism_parent_computes (C : Cat) (X : C)
  : MonoidToSemigroup (EndMonoid C X) = EndSemigroup C X.
Proof. reflexivity. Qed.

Example endomorphism_unit_computes (C : Cat) (X : C)
  : @monoid_unit _ (hasMonoid (EndMonoid C X)) = @id X.
Proof. reflexivity. Qed.

Section IndependentUniverses.
Universes u p l.
Constraint u < p, p < l.
Context (SA : Semigroup@{u p l}) (SB : Semigroup@{p u l})
    (HA : HasMonoid SA) (HB : HasMonoid SB).

Definition high_equality_monoid
  : Monoid@{u p l}
  := MonoidFromExtension SA HA.

Definition low_equality_monoid
  : Monoid@{p u l}
  := MonoidFromExtension SB HB.

Example high_carrier_coercion
  : (high_equality_monoid : SetC@{u p}) = (SA : SetC@{u p}).
Proof. reflexivity. Qed.

Example low_carrier_coercion
  : (low_equality_monoid : SetC@{p u}) = (SB : SetC@{p u}).
Proof. reflexivity. Qed.

End IndependentUniverses.
