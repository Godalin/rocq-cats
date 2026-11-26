From Stdlib Require Import
  Bool.
From Cats Require Import
  Algebra.Group.Transport.
From Cats Require Import
  Instance.Bool.Group.

Local Open Scope algebra_scope.

(** * A Transport Which Changes Representatives and the Unit

    Target representatives carry an irrelevant natural tag; equality retains
    an independent Boolean witness. Negating the Boolean in both directions
    transports xor to xnor and sends the source unit [false] to [true]. The
    inverse equations hold in specified equality, not native pair equality. *)

Definition tagged_equiv (x y : bool * nat)
  : Type
  := ((fst x = fst y) * bool)%type.

(** The equality laws preserve data; no proof irrelevance is assumed. *)

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

Program Definition to_bool
  : TaggedS →r BoolS
  :=
  {|func x := negb (fst x)
  |}.
Next Obligation. intros x y [H flag]. now rewrite H. Defined.

(** Returning chooses tag zero, so it cannot be a native inverse. *)

Program Definition from_bool
  : BoolS →r TaggedS
  :=
  {|func b := (negb b, 0)
  ; func_proper x y H := (f_equal negb H, false)
  |}.

(** Source recovery is native Boolean involution. *)

Definition source_recovery
  : (to_bool ∘r from_bool) ≈f id_resp.
Proof. intros []; reflexivity. Defined.

(** Target recovery uses specified equality and retains a witness flag. *)

Definition target_recovery
  : (from_bool ∘r to_bool) ≈f id_resp.
Proof. intros [[] n]; exact (eq_refl, true). Defined.

(** Explicitly select the transported group; no instance is exported. *)

Definition TaggedGroup
  : Group
  := GroupTransport BoolS_Group to_bool from_bool
      source_recovery target_recovery.

(** Computing all four products checks the transported operation, not just
    a proof of an inherited law. The payload is chosen by the return map. *)

Example product_table
  : (@mul _ (hasMagma TaggedGroup) (false, 4) (false, 7),
     @mul _ (hasMagma TaggedGroup) (false, 4) (true, 7),
     @mul _ (hasMagma TaggedGroup) (true, 4) (false, 7),
     @mul _ (hasMagma TaggedGroup) (true, 4) (true, 7)) =
    ((true, 0), (false, 0), (false, 0), (true, 0)).
Proof. vm_compute. reflexivity. Qed.

(** The transported unit and both inverses are actual returned values. *)

Example unit_inverse_values
  : (@mul_unit _ _ (hasUnit TaggedGroup),
     @inv _ _ _ (hasInverse TaggedGroup) (false, 19),
     @inv _ _ _ (hasInverse TaggedGroup) (true, 23)) =
    ((true, 0), (false, 0), (true, 0)).
Proof. vm_compute. reflexivity. Qed.

(** Target recovery does not preserve the original tag; the specified
    equality still holds with its explicitly retained Boolean witness. *)

Example recovery_value_and_witness
  : (from_bool (to_bool (false, 17)), snd (target_recovery (false, 17))) =
    ((false, 0), true).
Proof. vm_compute. reflexivity. Qed.

(** The selected product and unit remain definitionally those of the
    transported parent monoid all the way through the group bundle. *)

Example actual_parent
  : GroupToMonoid TaggedGroup = MonoidTransport BoolS_Group to_bool from_bool
      source_recovery target_recovery.
Proof. reflexivity. Qed.

(** Existing inverse Proper transports a genuine non-native equality,
    ignoring both different tags and different equality-witness flags. *)

Definition inverse_proper_client
  : @inv _ _ _ (hasInverse TaggedGroup) (false, 5) ≈S
      @inv _ _ _ (hasInverse TaggedGroup) (false, 81)
  := @inv_proper (GroupToMonoid TaggedGroup) _ (@isInverse _ _ _ (hasInverse TaggedGroup))
      (false, 5) (false, 81) (eq_refl, true).

(** Generic involution recovers the target element in specified equality. *)

Definition involution_client (x : TaggedS)
  : @inv _ _ _ (hasInverse TaggedGroup) (@inv _ _ _ (hasInverse TaggedGroup) x) ≈S x
  := @inv_inv TaggedGroup x.

(** Inverse uniqueness uses the exact inherited monoid and its laws. *)

Definition uniqueness_client (x y : TaggedS)
    (H : @mul _ (hasMagma TaggedGroup) y x ≈S
      @mul_unit _ _ (hasUnit TaggedGroup))
  : y ≈S @inv _ _ _ (hasInverse TaggedGroup) x
  := @inv_unique TaggedGroup x y H.

(** Generic inversion of a product applies without another inverse proof. *)

Definition product_inverse_client (x y : TaggedS)
  : @inv _ _ _ (hasInverse TaggedGroup) (@mul _ (hasMagma TaggedGroup) x y) ≈S
      @mul _ (hasMagma TaggedGroup)
        (@inv _ _ _ (hasInverse TaggedGroup) y) (@inv _ _ _ (hasInverse TaggedGroup) x)
  := @inv_mul TaggedGroup x y.

(** The three forward comparison equations apply to the very same group. *)

Definition product_comparison_client (x y : TaggedS)
  : to_bool (@mul _ (hasMagma TaggedGroup) x y) ≈S
      @mul _ (hasMagma BoolS_Group) (to_bool x) (to_bool y)
  := magma_transport_map_mul BoolS_Group to_bool from_bool
      source_recovery x y.

(** Unit comparison reads the original source unit. *)

Definition unit_comparison_client
  : to_bool (@mul_unit _ _ (hasUnit TaggedGroup)) ≈S
      @mul_unit _ _ (hasUnit BoolS_Group)
  := monoid_transport_map_unit BoolS_Group to_bool from_bool
      source_recovery target_recovery.

(** Inverse comparison reads the original source inverse. *)

Definition inverse_comparison_client (x : TaggedS)
  : to_bool (@inv _ _ _ (hasInverse TaggedGroup) x) ≈S
      @inv _ _ _ (hasInverse BoolS_Group) (to_bool x)
  := group_transport_map_inv BoolS_Group to_bool from_bool
      source_recovery target_recovery x.

(** Native equality is intentionally too strong for recovery and unit laws. *)

Fail Definition native_recovery
  : from_bool (to_bool (false, 17)) = (false, 17)
  := eq_refl.
Fail Definition native_unit_law
  : @mul _ (hasMagma TaggedGroup) (@mul_unit _ _ (hasUnit TaggedGroup))
      (false, 17) = (false, 17)
  := eq_refl.
Fail Definition no_implicit_model : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid) := ltac:(typeclasses eauto).

(** Native pairs support the same one-sided associative transport, even
    though target recovery and a unit for all tags are impossible. *)

Program Definition NativeTaggedS
  : SetC
  :=
  {|carrier := (bool * nat)%type
  ; carrier_equiv := eq
  ; carrier_setoid := eq_equivalence
  |}.

(** Both maps preserve native equality, independently of any inverse law. *)

Program Definition native_to_bool
  : NativeTaggedS →r BoolS
  :=
  {|func x := negb (fst x)
  |}.

(** The native return still chooses zero. *)

Program Definition native_from_bool
  : BoolS →r NativeTaggedS
  :=
  {|func b := (negb b, 0)
  |}.

(** Only source recovery is available. *)

Definition native_source_recovery
  : (native_to_bool ∘r native_from_bool) ≈f id_resp.
Proof. intros []; reflexivity. Defined.

(** The one-sided interface really constructs a semigroup in this example. *)

Definition NativeTaggedSemigroup
  : Semigroup
  := SemigroupTransport BoolS_Semigroup native_to_bool native_from_bool
      native_source_recovery.

(** The required law follows from that actual semigroup. *)

Definition native_associativity_client (x y z : NativeTaggedS)
  : @mul _ (hasMagma NativeTaggedSemigroup)
      (@mul _ (hasMagma NativeTaggedSemigroup) x y) z ≈S
      @mul _ (hasMagma NativeTaggedSemigroup) x
        (@mul _ (hasMagma NativeTaggedSemigroup) y z)
  := @mul_assoc _ _ (isSemigroup NativeTaggedSemigroup) x y z.

(** Every possible left factor produces tag zero, so no left unit can
    recover the element with tag one. This is a genuine missing hypothesis. *)

Example no_native_left_unit (e : NativeTaggedS)
  : @mul _ (hasMagma NativeTaggedSemigroup) e (false, 1%nat) ≠ (false, 1%nat).
Proof. intros H. pose proof (f_equal snd H) as K. discriminate K. Qed.

(** The omitted target recovery cannot be supplied by native reflexivity. *)

Fail Definition native_target_recovery
  : (native_from_bool ∘r native_to_bool) ≈f id_resp
  := λ x, eq_refl.
Fail Definition one_sided_is_not_monoid : Monoid
  := MonoidTransport BoolS_Monoid native_to_bool native_from_bool
      native_source_recovery.
