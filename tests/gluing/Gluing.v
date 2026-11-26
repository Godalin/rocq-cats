From Cats Require Import
  Cat.Gluing.Cartesian
  Cat.Diagram.Core
  Cat.Functor.Cartesian
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product.
From Stdlib Require Import Bool.Bool.

(** * Gluing Interfaces and Computational Mediators

    Check opposite strict orders for native hom and equality levels.
    Concrete setoid tests retain nontrivial equivalence witnesses and
    compute the two component mediators without inspecting square proofs. *)

(** ** Equality above the Glued Hom Carrier

    Fix [ed < hd < hc < ec < o < l]. The result keeps hom bound [hc]
    and equality bound [ec]; no native endpoint bound is identified. *)

Section LargeEquality.
Universes ed hd hc ec o l.
Constraint ed < hd, hd < hc, hc < ec, ec < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).

(** The comma wrapper preserves the strict output separation. *)

Definition gluing_large_equality
  : Cat@{o hc ec l l}
  := Gluing F.

(** The weak terminal theorem needs no chosen target terminal. *)

Definition gluing_large_equality_terminal (T : @Ob C) (HT : is_terminal T)
  : @is_terminal (Gluing F) (GluingTerminal F T)
  := gluing_terminal F T HT.

(** Product witnesses also retain the larger equality bound. *)

Definition gluing_large_equality_products
    `{PC : !HasProduct C} `{PD : !HasProduct D}
    (preserves : ∀ X Y : @Ob C,
      is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2))
  : HasProduct (Gluing F)
  := Gluing_HasProduct F preserves.

End LargeEquality.

(** ** Equality below the Glued Hom Carrier

    Reverse the native orders: [ec < hd < ed < hc < o < l]. The square
    witness fits [hc], while the resulting equality can stay at [ed]. *)

Section SmallEquality.
Universes ec hd ed hc o l.
Constraint ec < hd, hd < ed, ed < hc, hc < o, o < l.
Context {C : Cat@{o hc ec l l}} {D : Cat@{o hd ed l l}} (F : Fct C D).

(** The same construction accepts the reverse strict separation. *)

Definition gluing_small_equality
  : Cat@{o hc ed l l}
  := Gluing F.

(** The product construction does not equate these native levels. *)

Definition gluing_small_equality_products
    `{PC : !HasProduct C} `{PD : !HasProduct D}
    (preserves : ∀ X Y : @Ob C,
      is_product (F X) (F Y) (F ((X × Y)%ob)) (fmap F π1) (fmap F π2))
  : HasProduct (Gluing F)
  := Gluing_HasProduct F preserves.

End SmallEquality.

(** ** A Setoid with Observable Equality Witnesses

    Only the natural-number component is compared. A Boolean token is
    retained in each equality witness, and the carrier's Boolean tag is
    ignored. Thus neither equality nor witness data is native identity. *)

Program Definition TaggedGluingS
  : SetC
  :=
  {|carrier := (nat * bool)%type
  ; carrier_equiv x y := ((fst x = fst y) * bool)%type
  |}.
Next Obligation.
  split.
  - intros x. exact (eq_refl, false).
  - intros x y [h token]. exact (eq_sym h, token).
  - intros x y z [h token] [k other]. exact (eq_trans h k, token).
Defined.

(** A respectful map changes the ignored tag. *)

Program Definition gluing_toggle
  : TaggedGluingS →r TaggedGluingS
  :=
  {|func x := (fst x, negb (snd x))
  |}.
Next Obligation. intros x y [h token]. exact (h, token). Defined.

(** ** Explicit Chosen Structures in the Concrete Model

    Enable terminal and product choices only in this test section. The
    glued product reuses the identity functor's preserved product cones. *)

Section SetoidGluing.

(** Select the constructed gluing products locally. *)

Local Instance identity_gluing_products
  : HasProduct (Gluing (@IdF SetCat))
  := Gluing_HasProduct IdF (λ X Y, product_universal).

(** A glued object with the identity structure arrow. *)

Program Definition TaggedGluingObj
  : @Ob (Gluing (@IdF SetCat))
  :=
  {|comma_left_ob := TaggedGluingS
  ; comma_right_ob := TaggedGluingS
  ; comma_arrow := id
  |}.

(** Both components change the ignored tag; the square commutes by
    designated equality, with an observable token in its witness. *)

Program Definition tagged_gluing_toggle
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj TaggedGluingObj
  :=
  {|comma_left := gluing_toggle
  ; comma_right := gluing_toggle
  |}.
Next Obligation. intros [n b]. exact (eq_refl, true). Defined.

(** Native differences in tags do not change the glued arrow's equality. *)

Definition tagged_gluing_toggle_equal
  : tagged_gluing_toggle ≈ id.
Proof. split; intros [n b]; exact (eq_refl, true). Defined.

(** The universal mediator computes both diagonal functions. *)

Definition tagged_gluing_diagonal
  : (@Hom (Gluing (@IdF SetCat))) TaggedGluingObj
      ((TaggedGluingObj × TaggedGluingObj)%ob)
  := ⟨id, id⟩.

(** Computing the left component does not evaluate the square witness. *)

Example tagged_gluing_left_computes
  : comma_left tagged_gluing_diagonal (3, false) =
      ((3, false), (3, false)).
Proof. reflexivity. Defined.

(** The right component is the same transparent base mediator. *)

Example tagged_gluing_right_computes
  : comma_right tagged_gluing_diagonal (4, true) =
      ((4, true), (4, true)).
Proof. reflexivity. Defined.

(** Pairing respects nontrivial equality on both component maps. *)

Example tagged_gluing_pair_respects
  : ⟨tagged_gluing_toggle, tagged_gluing_toggle⟩ ≈ tagged_gluing_diagonal.
Proof.
  apply product_pair_proper; exact tagged_gluing_toggle_equal.
Defined.

(** The right projection's finite-product preservation is explicitly enabled. *)

Definition identity_gluing_right_cartesian
  : IsCartF (GluingRightF (@IdF SetCat)) (Gluing_HasTerminal IdF)
      identity_gluing_products
  := GluingRight_IsCartF IdF (λ X Y, product_universal).

(** ** Terminality without Preservation by the Gluing Functor

    A constant functor at the tagged setoid does not preserve terminality.
    Its gluing still has the constructed terminal. This concrete boundary
    prevents accidentally strengthening the terminal interface later. *)

(** Constant points witness that the tagged setoid is not terminal. *)

Program Definition tagged_gluing_point (n : nat)
  : UnitS →r TaggedGluingS
  :=
  {|func _ := (n, false)
  |}.
Next Obligation. intros x y h. exact (eq_refl, true). Defined.

(** Its points zero and one are inequivalent in the specified equality. *)

Definition tagged_gluing_not_terminal (H : is_terminal TaggedGluingS)
  : Empty_set.
Proof.
  destruct (H UnitS) as [h unique].
  assert (same : tagged_gluing_point 0 ≈f tagged_gluing_point 1).
  { transitivity h; [apply unique; exact I |
      symmetry; apply unique; exact I]. }
  destruct (same tt) as [impossible token]. discriminate impossible.
Defined.

(** The gluing terminal requires no image-terminal hypothesis. *)

Definition constant_gluing_terminal
  : @is_terminal (Gluing (ConstF SetCat TaggedGluingS))
      (GluingTerminal (ConstF SetCat TaggedGluingS) UnitS)
  := gluing_terminal _ _ terminal_universal.

(** Its left projection is demonstrably not terminal. *)

Definition constant_gluing_left_not_terminal
  : is_terminal (GluingLeftF (ConstF SetCat TaggedGluingS)
      (GluingTerminal (ConstF SetCat TaggedGluingS) UnitS)) → Empty_set
  := tagged_gluing_not_terminal.

(** The left terminal mediator still computes to the unchanged value. *)

Example constant_gluing_terminal_computes
  : comma_left (@term (Gluing (ConstF SetCat TaggedGluingS))
      (Gluing_HasTerminal
      (ConstF SetCat TaggedGluingS))
      (GluingTerminal (ConstF SetCat TaggedGluingS) UnitS)) (9, true) =
      (9, true).
Proof. reflexivity. Defined.

End SetoidGluing.
