From Cats Require Import
  Instance.Set.Lift
  Instance.Set.PresheafDescent
  Instance.Set.Sieve.Matching.
From Cats.Set Require Import
  Pi
  Subset.

(** * Independent Source, Target and Index Sizes *)

(** ** Equality Below the Carrier

    The category, hom data and generator index are larger than the value
    carriers. Equality lies below the carrier in the first profile and
    above it in the second. No coherent or respectful cover is assumed. *)

Section LowerEquality.
Universes l u p r s.
Constraint l < u, u < p, p < r, r < s.
Context {C : Cat@{r r s _ _}}
    {Q : Fct (C^op) SetCat@{p u _ _ _ _ _}}
    {P : Fct (C^op) SetCat@{p u _ _ _ _ _}}
    {I : Type@{r}} {D : I → @Ob C} (e : ∀ i, Q (D i))
    (cover cover' : is_presheaf_cover e)
    (a b : ∀ i, P (D i))
    (H : presheaf_values_compatible e a)
    (K : presheaf_values_compatible e b).

(** The actual map keeps value carrier and equality bounds independent. *)

Definition lower_equality_descent
  : Q ⇒ P
  := PresheafDescendN e cover a H.

(** Any supplied factor may compute the value. *)

Definition lower_equality_factor X (x : Q X) i (h : (@Hom C) X (D i))
    (E : fmap Q h (e i) ≈S x)
  : lower_equality_descent X x ≈S fmap P h (a i)
  := presheaf_descend_factor e cover a H X x i h E.

(** Generator recovery uses no native equality. *)

Definition lower_equality_β i
  : lower_equality_descent (D i) (e i) ≈S a i
  := presheaf_descend_β e cover a H i.

(** Naturality supplies the compatibility of extracted values. *)

Definition lower_equality_η (α : Q ⇒ P)
  : PresheafDescendN e cover (λ i, α (D i) (e i))
      (presheaf_map_values_compatible e α) ≈N α
  := presheaf_descend_η e cover α.

(** The unique extension is compared by specified natural equality. *)

Definition lower_equality_universal
  : is_unique (R := @NatEq _ _ _ _)
      (λ α : Q ⇒ P, ∀ i, α (D i) (e i) ≈S a i) lower_equality_descent
  := presheaf_descend_universal e cover a H.

(** Generator equality detects map equality at these independent sizes. *)

Definition lower_equality_map_eq (α β : Q ⇒ P)
  : α ≈N β ↔ ∀ i, α (D i) (e i) ≈S β (D i) (e i)
  := presheaf_cover_map_eq e cover α β.

(** Different cover and overlap witnesses are permitted. *)

Definition lower_equality_independent (E : ∀ i, a i ≈S b i)
  : lower_equality_descent ≈N PresheafDescendN e cover' b K
  := presheaf_descend_proper e cover cover' a b H K E.

(** The existing subset and indexed-product equalities ignore proof data. *)

Definition lower_equality_resp
  : SubsetS (PiS I (λ i, P (D i))) (presheaf_values_compatible e) →r
      Nat_SetS Q P
  := presheaf_descend_resp e cover.

End LowerEquality.

(** ** Equality Above the Carrier

    The category, hom data and generator index are larger than the value
    carriers. Equality lies below the carrier in the first profile and
    above it in the second. No coherent or respectful cover is assumed. *)

Section HigherEquality.
Universes l u p r s.
Constraint l < u, u < p, p < r, r < s.
Context {C : Cat@{r s r _ _}}
    {Q : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    {P : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    {I : Type@{r}} {D : I → @Ob C} (e : ∀ i, Q (D i))
    (cover cover' : is_presheaf_cover e)
    (a b : ∀ i, P (D i))
    (H : presheaf_values_compatible e a)
    (K : presheaf_values_compatible e b).

(** The actual map keeps value carrier and equality bounds independent. *)

Definition higher_equality_descent
  : Q ⇒ P
  := PresheafDescendN e cover a H.

(** Any supplied factor may compute the value. *)

Definition higher_equality_factor X (x : Q X) i (h : (@Hom C) X (D i))
    (E : fmap Q h (e i) ≈S x)
  : higher_equality_descent X x ≈S fmap P h (a i)
  := presheaf_descend_factor e cover a H X x i h E.

(** Generator recovery uses no native equality. *)

Definition higher_equality_β i
  : higher_equality_descent (D i) (e i) ≈S a i
  := presheaf_descend_β e cover a H i.

(** Naturality supplies the compatibility of extracted values. *)

Definition higher_equality_η (α : Q ⇒ P)
  : PresheafDescendN e cover (λ i, α (D i) (e i))
      (presheaf_map_values_compatible e α) ≈N α
  := presheaf_descend_η e cover α.

(** The unique extension is compared by specified natural equality. *)

Definition higher_equality_universal
  : is_unique (R := @NatEq _ _ _ _)
      (λ α : Q ⇒ P, ∀ i, α (D i) (e i) ≈S a i) higher_equality_descent
  := presheaf_descend_universal e cover a H.

(** Generator equality detects map equality at these independent sizes. *)

Definition higher_equality_map_eq (α β : Q ⇒ P)
  : α ≈N β ↔ ∀ i, α (D i) (e i) ≈S β (D i) (e i)
  := presheaf_cover_map_eq e cover α β.

(** Different cover and overlap witnesses are permitted. *)

Definition higher_equality_independent (E : ∀ i, a i ≈S b i)
  : higher_equality_descent ≈N PresheafDescendN e cover' b K
  := presheaf_descend_proper e cover cover' a b H K E.

(** The existing subset and indexed-product equalities ignore proof data. *)

Definition higher_equality_resp
  : SubsetS (PiS I (λ i, P (D i))) (presheaf_values_compatible e) →r
      Nat_SetS Q P
  := presheaf_descend_resp e cover.

End HigherEquality.

(** ** The Existing Sieve Client

    Membership and indices fit in the common large value carrier. Its
    equality bound remains smaller and independent. *)

Section SieveClient.
Universes l u p r s.
Constraint l < u, u < p, p < r, r < s.
Context {C : Cat@{r p u _ _}} {A : @Ob C}
    {I : Type@{r}} {D : I → @Ob C} (g : ∀ i, Hom (D i) A)
    (P : Fct (C^op) SetCat@{s u _ _ _ _ _}).

(** The old interface still constructs a map with a large source. *)

Definition strict_sieve_descent (a : SieveMatching g P)
  : (SievePsh (GeneratedSieve D g) :
      Fct (C^op) SetCat@{s u _ _ _ _ _}) ⇒ P
  := SieveMatchingN g P a.

(** Retain the pre-refactor component expression, including Program's
    treatment of a dependent membership match. This compares computations,
    not respectfulness or naturality proof records. *)

Program Definition original_sieve_evaluation (a : SieveMatching g P)
    X (x : (SievePsh (GeneratedSieve D g) :
      Fct (C^op) SetCat@{s u _ _ _ _ _}) X)
  : P X
  := match (lower x).2 with
      | (i; (h; _)) => fmap P h (a i)
      end.

(** The original computation converts even at an opaque input element. *)

Definition sieve_evaluation_unchanged (a : SieveMatching g P)
    X (x : (SievePsh (GeneratedSieve D g) :
      Fct (C^op) SetCat@{s u _ _ _ _ _}) X)
  : strict_sieve_descent a X x = original_sieve_evaluation a X x
  := eq_refl.

End SieveClient.

(** ** Distinct Native Sizes by Explicit Inclusion

    Source and target have different native carrier/equality bounds.
    Their natural transformation uses ordinary independent upward lifts
    into a common SetCat, without equating either pair of native bounds. *)

Section NativeSizes.
Universes l u p r s.
Constraint l < u, u < p, p < r, r < s.
Context {C : Cat} {I : Type} {D : I → @Ob C}
    (Q : Fct (C^op) SetCat@{u l _ _ _ _ _})
    (P : Fct (C^op) SetCat@{l p _ _ _ _ _})
    (e : ∀ i, Q (D i)) (a : ∀ i, P (D i)).
Let Q'
  : Fct (C^op) SetCat@{r s _ _ _ _ _}
  := LiftF ∘F Q.
Let P'
  : Fct (C^op) SetCat@{r s _ _ _ _ _}
  := LiftF ∘F P.
Let e' (i : I)
  : Q' (D i)
  :=
  {|lower := e i|}.
Let a' (i : I)
  : P' (D i)
  :=
  {|lower := a i|}.
Context (cover : is_presheaf_cover e')
    (H : presheaf_values_compatible e' a').

(** No relation between native source/target bounds is inferred. *)

Definition native_lifted_descent
  : Q' ⇒ P'
  := PresheafDescendN e' cover a' H.

(** Generator recovery remains at the target's native equality. *)

Definition native_lifted_β i
  : lower (native_lifted_descent (D i) (e' i)) ≈S a i
  := lower (presheaf_descend_β e' cover a' H i).

End NativeSizes.
