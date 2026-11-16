From Cats Require Import
  Cat.Core
  Algebra.Monoid.Core
  Algebra.Monoid.Category
  Algebra.Monoid.Transport
  Instance.Bool.Group.

Local Open Scope monoid_scope.

(** * Fixed-Parent Monoid Extensions

    A chosen unit belongs to one specified semigroup. Repacking it must
    preserve both that parent and its own computational selection. *)

(** * 固定父结构的幺半群扩充

    选定单位元属于一个指定半群。重新包装须保留该父结构及其自身的计算选择。 *)

Section UnchosenExtension.
Context {M : SetC} (SG : Semigroup M).

Fail Definition unchosen_monoid_extension
  : HasMonoid SG
  := ltac:(typeclasses eauto).

End UnchosenExtension.

(** ** Two Extensions of One Parent

    Keep both choices available and pass their evidence explicitly. A second
    local choice must not change the first monoid's stored unit or laws. *)

(** ** 同一父结构的两份扩充

    同时保留两份选择并显式传递见证；另一局部选择不得改变首个幺半群保存的
    单位元或定律。 *)

Section IndependentChoices.
Context {M : SetC} (SG : Semigroup M) (H K : HasMonoid SG).

Example first_parent_is_preserved
  : MonoidSG (MonoidFromExtension SG H) = SG.
Proof. reflexivity. Qed.

Example first_extension_is_preserved
  : @hasMonoid M (MonoidFromExtension SG H) = H.
Proof. reflexivity. Qed.

Example first_unit_is_selected
  : @monoid_unit M (MonoidFromExtension SG H) =
      @monoid_chosen_unit M SG H.
Proof. reflexivity. Qed.

Example second_unit_is_selected
  : @monoid_unit M (MonoidFromExtension SG K) =
      @monoid_chosen_unit M SG K.
Proof. reflexivity. Qed.

Example selected_left_law (x : M)
  : @magma_mul M SG (@monoid_chosen_unit M SG H) x ≈S x
  := @monoid_unit_l M (MonoidFromExtension SG H) x.

Example selected_units_are_equivalent
  : @monoid_chosen_unit M SG H ≈S @monoid_chosen_unit M SG K.
Proof.
  exact (monoid_units_equiv SG _ _ (@isMonoid M SG H) (@isMonoid M SG K)).
Qed.

End IndependentChoices.

(** ** Distinct Computational Choices

    Indiscrete setoid equality permits native-distinct chosen units on one
    constant semigroup. Their algebraic equivalence does not identify their
    boolean computations or their law records. *)

(** ** 不同计算选择

    全关系广集相等允许同一常值半群具有原生不同的选定单位元；代数相等不会
    等同其布尔计算或定律记录。 *)

Program Definition IndiscreteBoolS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv _ _ := unit
  |}.
Next Obligation. split; repeat intro; exact tt. Defined.

Program Definition ConstantBoolMagma
  : Magma IndiscreteBoolS
  :=
  {|magma_mul _ _ := false
  |}.
Next Obligation. repeat intro; exact tt. Defined.

Program Definition ConstantBoolSemigroup
  : Semigroup IndiscreteBoolS
  :=
  {|SemigroupM := ConstantBoolMagma
  ; semigroup_assoc _ _ _ := tt
  |}.

Program Definition BoolUnitExtension (e : bool)
  : HasMonoid ConstantBoolSemigroup
  :=
  {|monoid_chosen_unit := e
  ; isMonoid :=
      {|monoid_unit_left _ := tt
      ; monoid_unit_right _ := tt
      |}
  |}.

Example false_unit_computes
  : @monoid_unit _
      (MonoidFromExtension ConstantBoolSemigroup (BoolUnitExtension false))
      = false.
Proof. reflexivity. Qed.

Example true_unit_computes
  : @monoid_unit _
      (MonoidFromExtension ConstantBoolSemigroup (BoolUnitExtension true))
      = true.
Proof. reflexivity. Qed.

(** ** Existing Concrete Clients and Independent Sizes

    The original xor and endomorphism units still compute. Both strict size
    orders remain available for extensions and their fixed-setoid views. *)

(** ** 已有具体客户端与独立大小

    原异或与自态射单位元仍可计算；扩充及其固定广集视图仍支持两种严格大小次序。 *)

Example xor_unit_computes
  : @monoid_unit BoolS BoolS_Monoid = false.
Proof. reflexivity. Qed.

Example endomorphism_parent_computes (C : Cat) (X : C)
  : MonoidSG (EndMonoid C X) = EndSemigroup C X.
Proof. reflexivity. Qed.

Example endomorphism_unit_computes (C : Cat) (X : C)
  : @monoid_unit (HomSet X X) (EndMonoid C X) = @id X.
Proof. reflexivity. Qed.

Section IndependentUniverses.
Universes u p l.
Constraint u < p.
Constraint p < l.
Context (A : SetC@{u p}) (B : SetC@{p u})
    (SA : Semigroup@{l u p} A) (SB : Semigroup@{l p u} B)
    (HA : HasMonoid SA) (HB : HasMonoid SB).

Definition high_equality_monoid
  : Monoid@{u p l} A
  := MonoidFromExtension SA HA.

Definition low_equality_monoid
  : Monoid@{p u l} B
  := MonoidFromExtension SB HB.

End IndependentUniverses.
