From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.FiniteProducts
  Cat.Natural
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.CCC.Core
  Cat.Induced
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Kripke
  Instance.Set.PresheafExponential.
From CatsTests.gluing Require Import
  Gluing.

(** * Presheaf Exponential Sizes and Original Function Values

    Check both strict world Hom/equality orders and both orders between
    the world-law and common semantic bounds. Concrete probes use all
    respectful endomorphisms as world arrows, with observable equality data. *)

(** ** Large World Laws

    Keep [e < h < o < u < l]; stored world laws need not fit the value bound. *)

Section LargeLaws.
Universes o h e l u.
Constraint e < h.
Constraint h < o.
Constraint o < u.
Constraint u < l.
Context (C : Cat@{o h e l l}).

(** Explicitly chosen exponentials keep these native world levels. *)

Definition presheaf_large_law_exponentials
  : @HasExponential (FctCat (C^op) SetCat@{u u _ _ _ _ _})
      (@FctCat_HasProduct _ _ SetCat_HasProduct)
  := Psh_HasExponential C.

(** The complete CCC has the same independent world and value bounds. *)

Definition presheaf_large_law_ccc
  : CCC
  := Psh_CCC C.

(** The complete bundle retains the original category at these native bounds. *)

Example presheaf_large_law_ccc_category
  : (Psh_CCC C : Cat) = FctCat (C^op) SetCat@{u u _ _ _ _ _}.
Proof. reflexivity. Qed.

End LargeLaws.

(** ** Small World Laws

    Reverse the Hom/equality order with [h < e < o < l < u]. *)

Section SmallLaws.
Universes o h e l u.
Constraint h < e.
Constraint e < o.
Constraint o < l.
Constraint l < u.
Context (C : Cat@{o h e l l}).

(** The opposite strict orders also instantiate the chosen CCC. *)

Definition presheaf_small_law_ccc
  : CCC
  := Psh_CCC C.

(** The complete bundle retains the original category at these native bounds. *)

Example presheaf_small_law_ccc_category
  : (Psh_CCC C : Cat) = FctCat (C^op) SetCat@{u u _ _ _ _ _}.
Proof. reflexivity. Qed.

End SmallLaws.

(** ** Future-World Computation

    Oppose an induced category with two labels and all respectful maps
    between the same tagged setoid. Its presheaf acts by the original maps,
    so a future arrow can change an ignored representation tag. *)

Section TaggedWorlds.

(** Use the existing induced category and opposite construction. *)

Definition TaggedWorlds
  : Cat
  := (InducedCat bool (λ _, TaggedGluingS))^op.

(** The original inclusion diagram is read on the double opposite. *)

Definition TaggedPsh
  : Fct (TaggedWorlds^op) SetCat
  := @CompF (TaggedWorlds^op) (InducedCat bool (λ _, TaggedGluingS))
      SetCat (InducedInclusionF bool (λ _, TaggedGluingS))
      (@FromDoubleOpF (InducedCat bool (λ _, TaggedGluingS))).

(** A future arrow changes the observable natural-number coordinate. *)

Program Definition tagged_advance_resp
  : TaggedGluingS →r TaggedGluingS
  :=
  {|func x := (S (fst x), snd x)
  |}.
Next Obligation.
  intros [n b] [m c] [Hnm token]. exact (f_equal S Hnm, token).
Defined.

Local Instance tagged_pointwise_products
  : HasProduct (FctCat (TaggedWorlds^op) SetCat)
  := @FctCat_HasProduct _ _ SetCat_HasProduct.

Local Instance tagged_presheaf_exponentials
  : HasExponential tagged_pointwise_products
  := Psh_HasExponential TaggedWorlds.

(** The selected exponential keeps the existing coherent function presheaf. *)

Definition TaggedExpPsh
  : Fct (TaggedWorlds^op) SetCat
  := @exp (FctCat (TaggedWorlds^op) SetCat) tagged_pointwise_products
      tagged_presheaf_exponentials TaggedPsh TaggedPsh.

(** Transpose the context projection using the new selected structure. *)

Definition TaggedCurryN
  : TaggedPsh ⇒ TaggedExpPsh
  := @Cats.Cat.Exponential.Core.curry
      (FctCat (TaggedWorlds^op) SetCat) tagged_pointwise_products
      tagged_presheaf_exponentials _ _ _
      (PointwiseFstN _ _ TaggedPsh TaggedPsh).

(** A future world arrow actually transports the stored context value. *)

Example presheaf_curry_future_computes
  : TaggedCurryN false (3%nat, false) true tagged_advance_resp (7%nat, true)
      = (4%nat, false).
Proof. reflexivity. Qed.

(** Current-world evaluation keeps the untransported representation. *)

Example presheaf_curry_current_computes
  : TaggedCurryN false (3%nat, false) false id (7%nat, true)
      = (3%nat, false).
Proof. reflexivity. Qed.

(** Restriction followed by current-world evaluation computes as well. *)

Example presheaf_restricted_eval_computes
  : kripke_eval TaggedPsh TaggedPsh
      (fmap TaggedExpPsh (X := false) (Y := true)
        tagged_advance_resp (TaggedCurryN false (4%nat, false))) (8%nat, true)
      = (5%nat, false).
Proof. reflexivity. Qed.

(** The selected evaluation arrow computes on a natural pair. *)

Example presheaf_selected_eval_computes
  : (@Cats.Cat.Exponential.Core.eval
      (FctCat (TaggedWorlds^op) SetCat) tagged_pointwise_products
      tagged_presheaf_exponentials TaggedPsh TaggedPsh)
        false (TaggedCurryN false (5%nat, true), (9%nat, false))
      = (5%nat, true).
Proof. reflexivity. Qed.

(** The native transpose accepts context equality with different tags. *)

Example presheaf_curry_context_equal
  : TaggedCurryN false (3%nat, false) ≈S
      TaggedCurryN false (3%nat, true).
Proof.
  exact (@func_proper _ _ (TaggedCurryN false)
    (3%nat, false) (3%nat, true) (eq_refl, true)).
Defined.

(** Its pointwise equality still carries Boolean evidence. *)

Definition presheaf_curry_equality_token
  : bool
  := snd (presheaf_curry_context_equal true gluing_toggle (7%nat, false)).

(** Reuse the old native function values: only the model packaging is new. *)

Example presheaf_curry_original_application
    (X Y : bool) (z a : TaggedGluingS)
    (f : (@Hom TaggedWorlds) Y X)
  : TaggedCurryN X z Y f a ≈S
      kripke_curry_at TaggedPsh TaggedPsh TaggedPsh
        (PointwiseFstN _ _ TaggedPsh TaggedPsh) X z Y f a.
Proof. reflexivity. Qed.

End TaggedWorlds.
