From Cats Require Import
  Cat.Core
  Algebra.Monoid.Category
  Algebra.Monoid.Transport
  Instance.Bool.Group.

Local Open Scope algebra_scope.

(** * Complete Monoids and Fixed-Parent Choices

    Complete objects own their carrier. Extensions remain indexed by one
    selected parent; importing a model must not select an extension. *)

Section UnchosenExtension.
Context (SG : Semigroup).

Fail Definition unchosen_monoid_extension
  : @HasUnit SG (Semigroup_hasMagma SG)
  := ltac:(typeclasses eauto).

End UnchosenExtension.

(** ** Two Extensions of One Parent

    Both choices stay available; packing reads the supplied evidence. *)

Section IndependentChoices.
Context (SG : Semigroup) (H K : @HasUnit SG (Semigroup_hasMagma SG)).

Example first_parent_is_preserved
  : MonoidToSemigroup (MonoidOfSemigroup SG H) = SG.
Proof. destruct SG. reflexivity. Qed.

Example first_extension_is_preserved
  : hasUnit (MonoidOfSemigroup SG H) = H.
Proof. reflexivity. Qed.

Example first_unit_is_selected
  : @mul_unit _ _ (hasUnit (MonoidOfSemigroup SG H)) =
      @mul_unit SG _ H.
Proof. reflexivity. Qed.

Example selected_units_are_equivalent
  : @mul_unit SG _ H ≈S @mul_unit SG _ K.
Proof.
  exact units_equiv.
Qed.

End IndependentChoices.

(** ** Distinct Computational Choices

    Bool-valued indiscrete equality permits different native units and law
    tokens. Competing local instances must not replace stored selections. *)

Program Definition IndiscreteBoolS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv _ _ := bool
  |}.
Next Obligation. split; repeat intro; exact true. Defined.

Program Definition ConstantBoolMagma
  : Magma
  := MakeMagma IndiscreteBoolS
    {|mul _ _ := false
    ; mul_proper _ _ _ _ _ _ := true
    |}.

Program Definition ConstantBoolSemigroup
  : Semigroup
  := let M := ConstantBoolMagma in
     SemigroupOfMagma M
       {|mul_assoc _ _ _ := true|}.

(** Different operations and associativity witnesses on the same carrier
    remain separate computational choices. *)

Program Definition TrueMultiplication
  : HasMagma IndiscreteBoolS
  :=
  {|mul _ _ := true
  ; mul_proper _ _ _ _ _ _ := false
  |}.

Definition TrueMagma
  : Magma
  := MakeMagma IndiscreteBoolS TrueMultiplication.

Local Existing Instance TrueMultiplication.

Program Definition OtherAssociativity
  : @IsSemigroup ConstantBoolMagma (hasMagma ConstantBoolMagma)
  := {|mul_assoc _ _ _ := false|}.

Local Existing Instance OtherAssociativity.

Definition OtherSemigroup
  : Semigroup
  := SemigroupOfMagma ConstantBoolMagma OtherAssociativity.

Example stored_multiplications_compute
  : (@mul _ (hasMagma ConstantBoolMagma) false false,
      @mul _ (hasMagma TrueMagma) false false) = (false, true).
Proof. reflexivity. Qed.

(** Shared notation follows the typed magma, including both respectful
    sections, even with another multiplication on the same setoid. *)

Example notation_stored_multiplications
  : ((false : ConstantBoolMagma) ⋅ false,
      (false : TrueMagma) ⋅ false,
      ((false : ConstantBoolMagma) ⋅−) false,
      (−⋅ (false : TrueMagma)) false) = (false, true, false, true).
Proof. reflexivity. Qed.

Example stored_associativities_compute
  : (@mul_assoc _ _ (isSemigroup ConstantBoolSemigroup) true false true,
      @mul_assoc _ _ (isSemigroup OtherSemigroup) true false true) = (true, false).
Proof. reflexivity. Qed.

Example inherited_magma_carrier
  : (ConstantBoolSemigroup : SetC) = IndiscreteBoolS.
Proof. reflexivity. Qed.

Program Definition BoolUnitExtension (e t : bool)
  : @HasUnit ConstantBoolSemigroup (Semigroup_hasMagma ConstantBoolSemigroup)
  :=
  {|mul_unit := e
  ; isUnit :=
      {|mul_unit_l _ := t
      ; mul_unit_r _ := negb t
      |}
  |}.

Definition FalseUnit
  : @HasUnit ConstantBoolSemigroup (Semigroup_hasMagma ConstantBoolSemigroup)
  := BoolUnitExtension false false.

Definition TrueUnit
  : @HasUnit ConstantBoolSemigroup (Semigroup_hasMagma ConstantBoolSemigroup)
  := BoolUnitExtension true true.

Local Existing Instance FalseUnit.
Local Existing Instance TrueUnit.

Definition FirstMonoid
  : Monoid
  := MonoidOfSemigroup ConstantBoolSemigroup FalseUnit.

Definition SecondMonoid
  : Monoid
  := MonoidOfSemigroup ConstantBoolSemigroup TrueUnit.

Example stored_units_compute
  : (@mul_unit _ _ (hasUnit FirstMonoid),
      @mul_unit _ _ (hasUnit SecondMonoid)) = (false, true).
Proof. reflexivity. Qed.

(** The same numeral reads different units from the explicitly typed bundles. *)

Example notation_stored_units
  : ((1 : FirstMonoid), (1 : SecondMonoid)) = (false, true).
Proof. reflexivity. Qed.

Example stored_left_laws_compute
  : (@mul_unit_l _ _ _ (@isUnit _ _ (hasUnit FirstMonoid)) false,
      @mul_unit_l _ _ _ (@isUnit _ _ (hasUnit SecondMonoid)) false) =
      (false, true).
Proof. reflexivity. Qed.

Example stored_right_laws_compute
  : (@mul_unit_r _ _ _ (@isUnit _ _ (hasUnit FirstMonoid)) true,
      @mul_unit_r _ _ _ (@isUnit _ _ (hasUnit SecondMonoid)) true) =
      (true, false).
Proof. reflexivity. Qed.

(** The actual category constructor reads these same stored law tokens. *)

Example category_laws_use_stored_choices
  : (@comp_id_l (MonoidCat FirstMonoid) tt tt false,
      @comp_id_r (MonoidCat FirstMonoid) tt tt false,
      @comp_assoc (MonoidCat FirstMonoid) tt tt tt tt false false false) =
      (false, true, true).
Proof. reflexivity. Qed.

Fail Definition native_units_equal
  : @mul_unit _ _ (hasUnit FirstMonoid) =
      @mul_unit _ _ (hasUnit SecondMonoid)
  := eq_refl.

(** ** Concrete Clients and Independent Sizes

    Actual model projections compute. Strict sizes concern mathematical
    independence, not historical universe-argument positions. *)

Example xor_unit_computes
  : @mul_unit _ _ (hasUnit BoolS_Monoid) = false.
Proof. reflexivity. Qed.

Example endomorphism_parent_computes (C : Cat) (X : C)
  : MonoidToSemigroup (EndMonoid C X) = EndSemigroup C X.
Proof. reflexivity. Qed.

Example endomorphism_unit_computes (C : Cat) (X : C)
  : @mul_unit _ _ (hasUnit (EndMonoid C X)) = id[X].
Proof. reflexivity. Qed.

Section IndependentUniverses.
Universes u p l.
Constraint u < p, p < l.
Context (SA : Semigroup@{u p l}) (SB : Semigroup@{p u l})
    (HA : @HasUnit SA (Semigroup_hasMagma SA)) (HB : @HasUnit SB (Semigroup_hasMagma SB)).

Definition high_equality_monoid
  : Monoid@{u p l}
  := MonoidOfSemigroup SA HA.

Definition low_equality_monoid
  : Monoid@{p u l}
  := MonoidOfSemigroup SB HB.

Example high_carrier_coercion
  : (high_equality_monoid : SetC@{u p}) = (SA : SetC@{u p}).
Proof. reflexivity. Qed.

Example low_carrier_coercion
  : (low_equality_monoid : SetC@{p u}) = (SB : SetC@{p u}).
Proof. reflexivity. Qed.

End IndependentUniverses.
